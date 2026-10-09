/* Synth1 AudioWorkletProcessor — renders the whole synth on the audio thread.
 * Zero main-thread UI jitter / GC pauses: all DSP state lives here and is
 * mutated only via port messages posted from synth_engine.js.
 *
 * Message protocol (port.onmessage, ev.data):
 *   {t:'p',   id, v}      single param (panel step index)
 *   {t:'ps',  m}          bulk params {id:index}
 *   {t:'on',  note, vel}  note on  (vel 1..127)
 *   {t:'off', note}       note off (honours sustain pedal)
 *   {t:'pb',  v}          pitch bend -8192..8191 (14-bit, centre 0)
 *   {t:'sus', on}         CC64 damper pedal
 *   {t:'mod', v}          CC1 mod wheel 0..127
 *   {t:'panic'}           kill all voices
 *   {t:'tempo', v}        engine BPM for the arpeggiator beat grid (default 120)
 *
 * Params 31/32/33/34/59 (arp type/oct/beat/gate/on-off) drive the embedded
 * CArpeggiator (spec_lfo_fx.md §7); when arp on, 'on'/'off' feed its held-key
 * tracker and the arp re-voices at step boundaries (note-off at the gate edge).
 *
 * Params 52/53/54/55/56/66 (chorus delay/depth/rate/fb/level/on-off), 82/83/98
 * (delay type/spread/tone), 90 (pan) and 73/84/93 (unison on/spread/count) drive
 * the post-voice stereo FX chain (reports/fx_chain_report.md): per-voice pan
 * spread + mixer law -> CPan -> CDelay (chainMode dry/wet split) -> CChorus.
 *
 * Param ids follow web/spec/params.json. DSP laws ported from the repaired
 * C++ core (synth1fix.md stages 3-5):
 *   osc2 pitch/fine/kbd (params 2/3/4, FUN_18003bb00/3bba0), key shift 9,
 *   fine12 72 with the 62..66 dead zone, two-saw pulse (FUN_180051db0),
 *   three-way mix law (FUN_18003b8c0) + sub oscillator (95/96/97),
 *   filter keytrack centred on note 48 (FUN_180038070), env headroom clamp
 *   (FUN_180038140), leveler before soft-clip (FUN_18003af70/3a920),
 *   LFO dest routing osc2-only / both / filter mirror-fold (FUN_18003dbe0 /
 *   FUN_18003ad50) and mod-env dest 0 = osc2 pitch only.
 */
'use strict';

function clamp(v, lo, hi) { return v < lo ? lo : v > hi ? hi : v; }

var OSC1_WAVE = ['sine', 'triangle', 'sawtooth', 'square'];
var OSC2_WAVE = ['triangle', 'sawtooth', 'square', 'noise'];
var SUB_WAVE = ['sine', 'triangle', 'sawtooth', 'square'];   // param 96 (kSubShape)
/* panel step -> Waveform code (0 sine,1 saw,2 pulse,3 triangle,4 noise,5 square).
 * The engine dispatch (engine.cpp case 0/1) sets osc_wave = the raw .sy1 band,
 * so the worklet code must equal the raw enum: osc1 raw 0..3 = sine/saw/pulse/
 * tri, osc2 raw 1..4 = saw/pulse/tri/noise (panel step for osc2 is raw-1), and
 * the sub shape uses kSubShape = {sine,triangle,saw,square} indexed by raw. */
var OSC1_CODE = [0, 1, 2, 3];
var OSC2_CODE = [1, 2, 3, 4];
var SUB_CODE = [0, 3, 1, 5];

/* Arpeggiator (spec_lfo_fx.md §7): BEAT[19] divisors in 1/24-beat units
 * (@0x180093000) and the panel-step -> engine-mode map for param 31
 * (GUI updown/up/down/random = 1/0/3/4; FUN_180002090 sets dir for mode 3). */
var ARP_BEAT = [96, 84, 72, 48, 42, 36, 32, 24, 21, 18, 16, 12, 9, 8, 6, 4, 3, 2, 1];
var ARP_MODE = [1, 0, 3, 4];

/* Post-voice stereo FX chain (reports/fx_chain_report.md §1, core/fx/*).
 * Signal order (§0/§9): voice mixer (per-voice pan) -> CPan(90) -> CDelay
 * (chainMode: chain buffer keeps wet·input, tone buffer carries dry·taps) ->
 * CChorus (off-path adds the tone buffer directly; on-path ring = (chain +
 * tone)·level). Effector (77..81) and CEq (60..63) are out of this port's
 * scope. Device sizes mirror the binary (no realtime allocation). */
var CHORUS_LINE_SIZE = 8192, CHORUS_LINE_MASK = 0x1FFF;
var CHORUS_SUB_BLOCK = 64, CHORUS_OSC_CLAMP = 0.9999;
var DELAY_LINE_SIZE = 131072, DELAY_LINE_MASK = 0x1FFFF;
var DELAY_FB_MAX = 0.999, DELAY_TAP_EPS = 0.1, DELAY_MAX_FRAMES = 2048;
var DELAY_BEAT_TABLE = [0, 1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 21, 24, 32, 36, 42, 48, 72, 84, 96];

/* chorus base delay (param 52, case 0x34 → FUN_180003f00), milliseconds:
 * u = x/127; u < 0.5 → 0.05·300^(2u)^0.6 ; u ≥ 0.5 → 30·u  (0.05 / 15.12 / 30 ms) */
function chorusBaseDelayMs(x) {
  var u = x / 127;
  return (u < 0.5) ? 0.05 * Math.pow(300, Math.pow(2 * u, 0.6)) : 30 * u;
}
function chorusRateHz(x) { return 0.02 * Math.pow(20000, x / 127); }      // param 54, case 0x36
function chorusDepth(x) { return (Math.pow(100, x / 127) - 1) / 99; }     // param 53, case 0x35
function chorusFb(x) { return (x - 64) / 64 * 0.99; }                     // param 55, case 0x37
function chorusLevel(x) { return x / 127; }                               // param 56, case 0x38

/* delay spread (param 83, case 0x53 → FUN_180006b80), seconds:
 * x == 64 → 0; else sign(x−64)·1e-4·1000^min(|x−64|/63,1)  (−0.1 / +0.1 s) */
function delaySpreadSec(x) {
  var d = x - 64;
  if (d === 0) return 0;
  var e = Math.abs(d) / 63; if (e > 1) e = 1;
  var s = 1e-4 * Math.pow(1000, e);
  return d < 0 ? -s : s;
}
function delaySyncSeconds(idx, tempo) {                                     // param 35, TB[20]
  idx = clamp(idx, 0, 19);
  return (DELAY_BEAT_TABLE[idx] * 60) / (tempo * 24);
}
function delayWetLevel(x) { return x > 64 ? (127 - x) / 63 : 1; }          // param 37, FUN_1800069e0
function delayDryLevel(x) { if (x > 64) return 1; if (x === 0) x = 1; return (x - 1) / 63; }

/* per-voice pan spread (param 84, FUN_180037250) + mixer pan law (FUN_180015a20)
 * + global CPan law (param 90). */
function panSpreadLaw(spread, i, N) {
  if (N < 2) return 0;
  return spread * (2 * ((i % N) / (N - 1)) - 1);
}
function mixerPanLaw(pan) {
  var gl = 1, gr = 1;
  if (pan > 0) gl = Math.max(1 - pan, 1e-7);
  else if (pan < 0) gr = Math.max(1 + pan, 1e-7);
  return { gl: gl, gr: gr };
}
function cpanLaw(x) {
  var p = (x <= 64) ? (x - 64) / 64 : (x - 64) / 63;
  if (p < -1) p = -1; if (p > 1) p = 1;
  return { gl: (p > 0) ? (1 - p) : 1, gr: (p < 0) ? (1 + p) : 1 };
}

/* panel step index -> raw .sy1 band (params whose step count != 128) */
function rawBand(id, k) {
  switch (id) {
    case 2: return Math.round(k * 127 / 120);
    case 3: case 72: return Math.round(k * 127 / 123);
    case 5: return Math.round(k * 127 / 100);
    case 9: return k - 24;
    case 37: return Math.round(k * 127 / 92);
    case 54: return Math.round(k * 127 / 115);
    case 83: return Math.round(k * 127 / 104);
    case 93: return Math.round(k * 127 / 6);
    default: return k;
  }
}

/* params 3 / 72 fine cents, dead zone bands 62..66 (FUN_180028fe0 3/0x48) */
function fineCents(band) {
  if (band < 0x3e) return band - 0x3e;
  if (band < 0x43) return 0;
  return band - 0x42;
}

/* unison per-voice pitch detune (engine.cpp FUN_180037130/1a0 + voice
 * update_base_pitch): detune = 100*(e^(p75/127)-1)/(e-1) cents spread across
 * the N slots; odd slots additionally shift by (p85-24)*100 cents. */
function unisonDetuneCents(raw75) {
  var x = raw75 / 127;
  return (Math.exp(x) - 1) / (Math.E - 1) * 100;
}
function unisonSlotPitchCents(slot, count, raw75, raw85) {
  if (count <= 1) return 0;
  var cents = unisonDetuneCents(raw75) * (slot / (count - 1) - 0.5);
  if ((slot & 1) !== 0) cents += (raw85 - 24) * 100;
  return cents;
}

/* param 21 bipolar filter-env amount (FUN_18003b670) */
function filterAmount(band) { return (band - 63) / 64; }

/* J (staged law): filter velocity scalar (core voice.h:122
 * filter_velocity_scale, FUN_18003a780, spec_env.md §4.3):
 * scale = (1 - exp(-1.1\u00b7vel/127)) / (1 - exp(-1.3));
 * CVcf+0xc0 = (int)(127\u00b7scale); scales the FE amount when param 24 is on. */
function filterVelScale127(vel) {
  var vv = clamp(vel | 0, 0, 127);
  var num = 1 - Math.exp(-1.1 * vv / 127);
  var den = 1 - Math.exp(-1.3);
  return Math.trunc(127 * (num / den));
}

/* ADSR time / sustain / gain / velocity laws (portable-synth/core/env/adsr.cpp
 * + velocity_curve.h): exponential param->seconds, 2048^(x^0.3)/2048 curves. */
function ampAttackSec(b) { return Math.pow(56000, b / 127) * 0.0005; }   // params 25/15/12
function ampDecaySec(b) { return Math.pow(6000, b / 127) * 0.01; }       // params 26/16/13
function ampReleaseSec(b) { return Math.pow(6000, b / 127) * 0.01; }     // params 28/18
function ampSustainRatio(b) { if (b === 0) return 0; return Math.pow(2048, Math.pow(b / 127, 0.3)) / 2048; }  // param 27
function ampGainCurve(b) { if (b === 0) return 0; return Math.pow(2048, Math.pow(b / 127, 0.3)) / 2048; }     // param 29
function velFactor(vel, sensBand) { return Math.pow(10, -1.5 * (sensBand / 127) * (127 - vel) / 127); }       // param 30

/* param 11 bipolar mod-env amount (FUN_18003e260) */
function modEnvAmount(band) {
  if (band === 0x40) return 0;
  if (band < 0x40) return band / 64 - 1;
  return (band - 0x40) / 63;
}

/* three-way osc mix law (FUN_18003b8c0) */
function mixGains(mix, subAmp) {
  var u1 = 1 - mix;
  var denom = (subAmp + 1) * u1 + mix;
  var norm = 1 / denom;
  var g1 = norm * u1;
  return { g1: g1, g2: norm * mix, gsub: g1 * subAmp };
}

/* pulse duty index (FUN_180051db0, spec_osc.md 6.2): d = pw*(1+pwMod/128)
 * (pwMod>=1: d = (2-pw)*pwMod/128 + pw), clamp [0.01,1.99], x1024 */
function pulseDutyIndex(pulseWidth, pwMod) {
  var d;
  if (pwMod < 1) d = (pwMod / 128 + 1) * pulseWidth;
  else d = (2 - pulseWidth) * pwMod / 128 + pulseWidth;
  d = clamp(d, 0.01, 1.99);
  return (d * 1024) | 0;
}

/* cutoff table T[i] = 15 * 1066.66667^(i/1024) (FUN_1800381f0) */
function fcOfIndex(i) { return 15 * Math.pow(1066.66667, i / 1024); }

/* filter keytrack (FUN_180038070): centre note 48 (C3), log-table index */
function keytrackIndex(i0, note, amt) {
  if (!(amt > 0)) return 0;
  var x = Math.pow(amt + 1, (note - 48) / 12);
  var hz = fcOfIndex(i0);
  var idx = Math.floor(1024 * Math.log(hz * x / 15) / Math.log(1066.66663));
  idx = clamp(idx, 0, 1024);
  return idx - i0;
}

/* filter env headroom clamp (FUN_180038140): amt in [f1-1, f1] */
function envHeadroom(i0, iKey, amt) {
  var f1 = (1024 - iKey - i0) / 1024;
  return clamp(amt, f1 - 1, f1);
}

/* LFO filter mirror-fold addend (FUN_18003ad50) */
function mirrorFoldAdd(i, m) { return ((m > 0 ? 1024 - i : i) * m) >> 10; }

/* ---------------- Band-limited wavetables (core/tables/wavetable_gen) ------
 * Tables are generated at build time (web/build_presets.js -> web/wavetables.js,
 * a base64 Float32 blob) and decoded once here (init-time, never in process()).
 * Layout: sine[2048], saw[36*2048], triangle[36*2048], square[36*2048]. */
var WT_SIZE = 2048, WT_BANDS = 37, WT = null;
function decodeWavetables() {
  if (WT) return WT;
  var b64 = (typeof globalThis !== 'undefined' && globalThis.SYNTH1_WAVETABLES) ||
            (typeof SYNTH1_WAVETABLES !== 'undefined' ? SYNTH1_WAVETABLES : null);
  if (!b64) return null;
  var bin = (typeof atob === 'function') ? atob(b64)
          : (typeof Buffer !== 'undefined' ? Buffer.from(b64, 'base64').toString('binary') : null);
  if (!bin) return null;
  var n = bin.length, bytes = new Uint8Array(n);
  for (var i = 0; i < n; i++) bytes[i] = bin.charCodeAt(i);
  var f32 = new Float32Array(bytes.buffer);
  var S = WT_SIZE, B = WT_BANDS;
  WT = {
    sine: f32.subarray(0, S),
    saw: f32.subarray(S, S + B * S),
    tri: f32.subarray(S + B * S, S + 2 * B * S),
    sq: f32.subarray(S + 2 * B * S, S + 3 * B * S)
  };
  return WT;
}

/* Band descriptors (spec_osc.md §5.1, FUN_18003cdf0 band law, legion 2026-10-08):
 * quarter-octave pitch ladder thr = 27.5·512^(j/36) while H = (int)(22050/thr)
 * ≥ 16 (23 bands, 27.5 … 1244.5 Hz, full Nyquist coverage), then the
 * integer-harmonic tail in groups of four (H 14 … 3) + the single tail (H 2, 1)
 * — 37 bands, thr ascending 27.5 … 22050. float32 to match the C++ exactly. */
var BAND_THR = new Float32Array(WT_BANDS);
var BAND_HARM = new Int32Array(WT_BANDS);
(function () {
  var n = 0, lastInt = 0, breakInt = 0;
  for (var j = 0; j < 0x24; j++) {
    var x = Math.fround(Math.fround(j) * 0.02777777798473835);
    var thr = Math.fround(Math.pow(512.0, x) * 27.5);
    var q = Math.fround(22050.0 / thr);
    if (q < 1.0) q = 1.0;
    var qi = q | 0;
    if (qi < 0x10) { breakInt = qi; break; }
    if (qi !== lastInt) {
      BAND_THR[n] = thr; BAND_HARM[n] = Math.trunc(Math.fround(22050.0 / thr));
      n++; lastInt = qi;
    }
  }
  var r = breakInt;
  if (3 < r) {
    var s = r - 2;
    for (;;) {
      var add = function (h) {
        var t = Math.fround(22050.0 / h);
        if (t < 1.0) t = 1.0;
        BAND_THR[n] = t; BAND_HARM[n] = Math.trunc(Math.fround(22050.0 / t));
        n++;
      };
      add(r); add(s + 1); add(s); add(s - 1);
      r -= 4; s -= 4;
      if (!(3 < r)) break;
    }
  }
  while (0 < r) {
    var t2 = Math.fround(22050.0 / r);
    if (t2 < 1.0) t2 = 1.0;
    BAND_THR[n] = t2; BAND_HARM[n] = Math.trunc(Math.fround(22050.0 / t2));
    n++; r--;
  }
})();

/* Wave index -> band table (spec_osc.md §5.6, FUN_18003cad0 verbatim):
 * binary search on the INTEGER part of the thresholds ((int)desc[mid].thr <=
 * (int)freq) over the 37 bands + the device's low-frequency step-back
 * (freq <= 1575 = 22050/14, the tail's first H). */
function selectBand(freq) {
  freq = Math.fround(freq);
  var lo = 0, hi = WT_BANDS - 1;
  var iF = freq | 0;
  while (lo < hi) {
    var mid = (lo + hi) >> 1;
    if ((BAND_THR[mid] | 0) <= iF) lo = mid + 1; else hi = mid;
  }
  if (freq !== BAND_THR[lo] && freq <= 1575.0 && lo > 0) lo--;
  return lo;
}

/* Wavetable readout (spec_osc.md §0): index (phase>>16)&0x7ff, fraction
 * (phase&0xffff)/65536, linear fused blend. phase is a 32-bit unsigned value. */
function readTable(table, phase) {
  var i = (phase >>> 16) & 0x7ff;
  var u = (phase & 0xffff) / 65536;
  return (table[(i + 1) & 0x7ff] - table[i]) * u + table[i];
}

/* Waveform codes (Waveform enum): 0 sine, 1 saw, 2 pulse, 3 triangle, 4 noise,
 * 5 square. Table selection mirrors core/tables get_table. */
function waveTable(wt, wave, freq) {
  if (!wt) return null;
  var b = selectBand(freq) * WT_SIZE;
  switch (wave) {
    case 0: return wt.sine;
    case 1: case 2: return wt.saw.subarray(b, b + WT_SIZE);
    case 3: return wt.tri.subarray(b, b + WT_SIZE);
    case 5: return wt.sq.subarray(b, b + WT_SIZE);
    default: return null;   // noise: no table
  }
}

/* 21-bit Galois LFSR noise (spec_osc.md §6.3, FUN_180051b30): seed 10, taps
 * 0x43, output from bit 19, advanced once per sample. */
function lfsrNext(v) {
  var s = v.lfsr >>> 0;
  var out = ((s >> 19) & 1) ? 1 : -1;
  if (((s >> 19) & 1) === 0) s = (s << 1) >>> 0;
  else s = (((s ^ 0x43) << 1) | 1) >>> 0;
  v.lfsr = s >>> 0;
  return out;
}

/* note-on phase init — the DEVICE law (voice.cpp FUN_18003e600 +
 * engine.cpp note_on_live, spec_phase.md §4). The phase LCG (DAT_1800938d4,
 * seed 1) is a stream SEPARATE from the CRT rand() stream (FUN_180055b98):
 * the DLL's statically-linked CRT keeps its own _holdrand, and every phase
 * consumer in the device reads THIS one, in device call order:
 *   band >= 1 (immobilize): EVERY note-on re-seeds from the fixed T table
 *     (spec §3, built at DLL load from a seed-1 LCG): osc1 = 0,
 *     osc2 = (int)((float)((band−1)·(1/126f))·2^26) & 0x7ffffff; with
 *     unison count > 1 and param92 = U·127 > 0, voice v's set shifts by
 *     U·T[10v+j]·2^27 (U = param92/127, j = 0/1 for osc1/osc2).
 *   band == 0: the per-VOICE FIRST note-on (reseed flag: voice ctor +
 *     patch-load loop, spec §2) consumes 10 draws: draw0 = osc1 phase,
 *     draw1 = osc2 phase (& 0x7ffffff), draws 2..9 = the 8 detune-tap slots
 *     (stream advance only — this port has no detune taps, like core).
 *     Every LATER note-on on that voice is Branch B: FREE-RUN — the phase
 *     accumulators are NOT touched and NOTHING is consumed.
 *   mono/legato first note with portamento on (param 39 ≠ 0): the engine
 *     primes 6 note-ons (60 draws) off the top before the voice's own 10
 *     (engine.cpp note_on_live prime_phase_init(6)).
 * Draw value: (int)((float)((double)((s>>16)&0x7fff)·3.05185095e-05)·
 * 134217728.0f) = rand15·2^12. */
var PHASE_LCG = 1;
function resetPhaseLcg() { PHASE_LCG = 1; }
function nextRandomPhase() {
  PHASE_LCG = (PHASE_LCG * 0x343fd + 0x269ec3) >>> 0;
  var f = Math.fround(((PHASE_LCG >> 16) & 0x7fff) * 3.05185095e-05);
  return Math.fround(f * 134217728.0) | 0;
}
function primePhaseLcg(n) { for (var d = 0; d < n * 10; d++) nextRandomPhase(); }
/* T = the immobilize phase table (.data 0x1800930d0, spec_phase.md §3):
 * T[i] = rand_i(srand 1)/32768 from the DLL-load LCG fill loop — its own
 * seed-1 stream, independent of PHASE_LCG. */
var PHASE_T = (function () {
  var t = new Float32Array(512), s = 1;
  for (var i = 0; i < 512; i++) {
    s = (Math.imul(s, 0x343FD) + 0x269EC3) >>> 0;
    t[i] = Math.fround(((s >> 16) & 0x7fff) / 32768);
  }
  return t;
})();
var PHASE_INV126 = Math.fround(1 / 126);
var PHASE_INV127 = Math.fround(1 / 127);

/* rational tanh Padé saturator (spec_filter.md §1.3, LPDL loop) */
function tanh3(e) {
  if (e < -3.0) return -1.0;
  if (e > 3.0) return 1.0;
  var e2 = e * e;
  return e * (e2 + 27.0) / (9.0 * e2 + 27.0);
}

/* ---- LFO control plane (core/lfo/lfo.cpp, spec_lfo_fx.md §1) ---- */
var LFO_DIV = [1536, 1152, 864, 768, 576, 432, 384, 288, 216, 192,
               144, 96, 84, 72, 48, 42, 36, 32, 24, 21, 18, 16, 12, 9, 8, 6, 4, 3, 2, 1];
/* The device's ONE CRT rand() stream (FUN_180055b98, core/rng/crt_rand.h):
 * MSVC LCG s = s*0x343FD + 0x269EC3, value (s >> 16) & 0x7FFF, _holdrand
 * starts at 1 and the DLL never calls srand(). Every random consumer shares
 * this stream in device call order: the LFO wave setter (FUN_180015450), the
 * LFO key-sync reset (FUN_1800152e0), the LFO period wrap (FUN_180014f60)
 * and the arpeggiator random mode (FUN_180001b40 -> rand()%(octaves+1), then
 * FUN_180001930 -> rand()%heldCount). The oscillator-phase LCG (PHASE_LCG,
 * DAT_1800938d4) is a SEPARATE stream and the noise osc is a per-voice LFSR. */
var CRT_HOLDRAND = 1;
function crtSrand(seed) { CRT_HOLDRAND = (seed === undefined ? 1 : seed) >>> 0; }
function crtRand() {
  CRT_HOLDRAND = (Math.imul(CRT_HOLDRAND, 0x343FD) + 0x269EC3) >>> 0;
  return (CRT_HOLDRAND >> 16) & 0x7FFF;
}
/* rand() % |hi-lo| + min(lo,hi), or hi when lo == hi (no draw) — the law shared
 * by FUN_180014f60 / FUN_1800152e0 / FUN_180015450. */
function lfoDrawSh(st) {
  var hi = st.hi, lo = st.lo;
  if (hi === lo) return hi;
  if (hi < lo) return crtRand() % (lo - hi) + hi;
  return crtRand() % (hi - lo) + lo;
}
var LFO_WAVE5 = null;
/* The wave-5 table (FUN_18003cad0(0, 0.0) -> DAT_1801a4298): T[i] =
 * (float)sin(i * 2pi * (1/2048)) * 1.0f — a 2048-entry SINE table. LFO wave 5
 * is a table sine, not noise (the spec's "noise" label was wrong). */
function lfoWave5Table() {
  if (LFO_WAVE5) return LFO_WAVE5;
  var t = new Float32Array(2048);
  for (var i = 0; i < 2048; i++) t[i] = Math.fround(Math.sin(i * 6.283185307179586 * 0.00048828125) * 1.0);
  LFO_WAVE5 = t; return t;
}
function lfoNoiseTable() { return lfoWave5Table(); }   /* legacy name (wave 5) */
function mkLfo(sr) {
  return { onOff: 0, wave: 0, dest: 0, tempoSync: 0, keySync: 0, speed: 0, depth: 0,
           sampleRate: sr || 44100, minSegment: 64, freqCur: 1.0, freqTarget: 1.0,
           lo: 0, hi: 0, phase: 0, period: 44100, rndCur: 0, rndNext: 0 };
}
/* speed -> Hz (FUN_180015210): free-run 1500^(s/127)/12; tempo-sync tempo*48/DIV[i]/120 */
function lfoHz(speed) { return Math.pow(1500, speed / 127) / 12; }
function lfoSpeedToHz(st, tempo) {
  var freq;
  if (st.tempoSync === 0) freq = Math.pow(1500, st.speed / 127) / 12;
  else { var i = (st.speed * 30) >> 7; if (i > 29) i = 29; freq = tempo * 48 / LFO_DIV[i] / 120; }
  st.freqTarget = freq; st.minSegment = (freq > 10) ? 32 : 64;
}
/* depth -> modulation range (FUN_180015080): exp pitch law, per-dest lo/hi */
function lfoRange(dest, depth) {
  var d = (dest === 1 || dest === 2) ? (Math.pow(10, depth / 127) - 1) / 9 : depth / 127;
  var f = Math.fround(d);
  switch (dest) {
    case 1: case 2: return { hi: (f * 5 * 128) | 0, lo: (f * -5 * 128) | 0 };
    case 3: return { hi: (f * 1024) | 0, lo: 0 };
    case 4: return { hi: 0, lo: (f * -2048) | 0 };
    case 5: return { hi: (f * 128) | 0, lo: (f * -128) | 0 };
    case 6: return { hi: (f * 512) | 0, lo: 0 };
    case 7: return { hi: (f * 64) | 0, lo: (f * -64) | 0 };
    default: return { hi: 0, lo: 0 };
  }
}
function lfoDepthToRange(st) { var r = lfoRange(st.dest, st.depth); st.hi = r.hi; st.lo = r.lo; }

/* FM depth law (voice.cpp FUN_18003bf50 @0x18003c33a, spec_osc.md §6.7):
 * gate = LFO dest6 (0..512) + signed mod-env dest1 (512 scale), clamped
 * ±512; amt' interpolates the raw amount toward 127 (gate>0) or 0 (gate<0);
 * depth = (1000^(amt'/127) − 1)·(1/999)·2^26 phase units (0..2^26). */
function fmDepthFromGate(amtBand, gate) {
  var n = gate;
  if (n > 512) n = 512;
  if (n < -512) n = -512;
  var amt = n > 0 ? amtBand + n * (127 - amtBand) / 512
                  : amtBand + n * amtBand / 512;
  if (amt <= 0) return 0;
  return (((Math.pow(1000, amt / 127) - 1) * (1 / 999) * 67108864) | 0);
}
/* COSRAMP (DAT_1801a32e0, spec_osc.md §6.7): (1 + cos(i·π/257))·0.5, 256
 * doubles. Index 256 (the first lookup, rem == rampTotal) reads zeroed BSS
 * → 0.0, so the ramp starts exactly at rampStart. */
var COSRAMP_TBL = null;
function cosRampTable() {
  if (COSRAMP_TBL === null) {
    var t = new Float64Array(256);
    for (var i = 0; i < 256; i++) t[i] = (1 + Math.cos(i * Math.PI / 257)) * 0.5;
    COSRAMP_TBL = t;
  }
  return COSRAMP_TBL;
}
/* FmRampState (core/osc/osc_dispatch.{h,cpp}, spec_osc.md §6.7) — FM depth
 * ramp state machine, run per sample (the core runs render_oscillators with
 * num_samples = 1, i.e. block_cur += 1 per sample, capped at rampMax =
 * (int)(sr/1000)). On a target change: big jump (|delta| >= 0x4000001) or
 * the end-of-release flag ⇒ snap (clears flag AND rampTotal, the 8-byte
 * zero store at cv+0xb8); otherwise ramp duration = samples the OLD target
 * was held, starting at the current depth; zero elapsed samples ⇒ rem 0 ⇒
 * snap. Per sample while ramping: every 32 samples (rem & 0x1f == 0, rem
 * BEFORE the decrement) depth = start + (int)((target−start)·COSRAMP
 * [(rem<<8)/total]); rem-- each sample; rem == 0 snaps. Returns the current
 * depth (0 when FM is fully off, i.e. depth == target == 0). */
function mkFmRamp() {
  return { depth: 0, start: 0, rem: 0, lastTarget: -1, flag: 0, total: 0, blockCur: 0 };
}
/* CVco note-on (FUN_18003db00): the first target check of the note runs with
 * zero hold time ⇒ depth snaps to the note-on target. */
function fmNoteOnReset(fm) { fm.lastTarget = -1; fm.blockCur = 0; }
/* CVco end-of-release (FUN_180037f00 → FUN_18003dfd0): the first target
 * change of the next note jumps (snap) instead of ramping. */
function fmReleaseReset(fm) { fm.flag = 1; }
function fmRampStep(fm, target, rampMax) {
  if (fm.lastTarget !== target) {
    var delta = fm.depth - target;
    if (delta < 0) delta = -delta;
    if (delta < 0x4000001 && fm.flag === 0) {
      if (fm.total <= fm.blockCur) {
        fm.total = fm.blockCur;   // ramp duration = time the old target held
        fm.rem = fm.blockCur;
        fm.start = fm.depth;
      }
    } else {
      fm.flag = 0;
      fm.total = 0;               // the snap: 8-byte zero store at cv+0xb8
      fm.depth = target;          // clears BOTH flag (0xb8) and rampTotal (0xbc)
    }
    if (fm.rem === 0) fm.depth = target;
    fm.blockCur = 0;
    fm.lastTarget = target;
  }
  if (fm.blockCur < rampMax) fm.blockCur++;
  if ((fm.depth !== 0 || target !== 0) && fm.depth !== target) {
    if (fm.rem > 0) {
      if ((fm.rem & 0x1f) === 0) {
        var idx = Math.floor((fm.rem << 8) / fm.total);
        var c = (idx >= 0 && idx < 256) ? cosRampTable()[idx] : 0.0;
        fm.depth = (((target - fm.start) * c) | 0) + fm.start;
      }
      fm.rem--;
    } else {
      fm.depth = target;
    }
  }
  return fm.depth;
}
/* Mod env (core env::ADSR + voice.cpp step_env_chunks, spec_env.md §2.3/§5):
 * AD envelope (sustain level 0), integer chunk levels on the dest scale
 * (640 pitch / 512 FM / 128 PW × |amount|, voice.h MOD_ENV_SCALE_*),
 * adaptive chunk walk FUN_18000c780 (chunks never span the render range),
 * dest 1 = LINEAR decay, others EXPONENTIAL (expf((r−1)·8)·r·delta). The
 * core runs the walk per sample (one level per chunk, applied to every
 * sample of the chunk). */
/* env::ADSR (core/env/adsr.h, spec_env.md §2.3 — FUN_18000ccc0 +
 * FUN_18000c780): the DEVICE envelope state machine. Integer levels (CVca
 * scale 2048, CVcf 1024), adaptive recompute marks, half-size chunks for
 * CVca (+0x34 = 1: chunk = recomputeAt/2, attack = ONE chunk, exponential
 * release ends early at 0.9·total DAT_180072b74). The CVca gain stage
 * (FUN_180037c30, voice.cpp step_env_chunks/process_full_sample) ramps its
 * applied gain LINEARLY across each chunk (g_step = (g_target − g_cur)/cl,
 * g += step per sample); CVcf holds its chunk level (stair-step). */
function mkAdsr(scale, half) {
  return { stage: 0, prog: 0, cur: 0, target: scale, susLevel: scale, off: 0,
           aS: 0, dS: 0, rS: 0, recompAt: 0, chunkLen: 1, susRatio: 1,
           dMode: 0, rMode: 0, half: half ? 1 : 0, scale: scale };
}
function adsrTimes(e, aS, dS, rS) {
  var old = e.aS;
  e.aS = aS;
  if (e.stage === 1 && old !== 0 && aS !== 0) e.prog = Math.trunc((e.prog * aS) / old);
  e.dS = dS; e.rS = rS;
}
function adsrSustain(e, ratio) {
  e.susRatio = ratio;
  e.susLevel = Math.trunc(e.scale * 1.0 * ratio);
}
function adsrAmount(e, aamt) {
  e.target = Math.trunc(e.scale * aamt);
  e.susLevel = Math.trunc(e.scale * aamt * e.susRatio);
}
function adsrNoteOn(e) {
  e.stage = 1;
  if (e.cur === 0) e.prog = 0;
  else e.prog = Math.trunc((e.aS * e.cur) / (e.target !== 0 ? e.target : 1));
  e.cur = 0; e.recompAt = 0;
}
function adsrNoteOff(e) {
  if ((e.stage & ~4) !== 0) {
    e.stage = 4; e.off = e.cur; e.prog = 0; e.recompAt = 0; adsrRecompute(e);
  }
}
function adsrReset(e) {
  e.stage = 0; e.cur = 0; e.prog = 0; e.off = 0; e.recompAt = 0; e.chunkLen = 1;
}
function adsrRecompute(e) {
  var dur, delta, mode;
  if (e.stage === 2) { dur = e.dS; delta = e.target - e.susLevel; mode = e.dMode; }
  else { dur = e.rS; delta = e.off; mode = e.rMode; }
  if (dur < 1) dur = 1;
  if (delta < 1) delta = 1;
  var rate = Math.trunc(dur / delta);
  if (mode === 1) {
    if (e.half) { e.recompAt = dur; e.chunkLen = dur > 1 ? dur : 1; return; }
    e.chunkLen = rate > 1 ? rate : 1; e.recompAt = dur; return;
  }
  var prev = e.recompAt;
  if (prev < Math.trunc(dur / 2)) {
    if (Math.trunc(dur / 3) <= prev) { e.recompAt = Math.trunc(dur / 2); e.chunkLen = rate * 2; }
    else if (Math.trunc(dur / 4) <= prev) { e.recompAt = Math.trunc(dur / 3); e.chunkLen = rate; }
    else if (Math.trunc(dur / 10) <= prev) { e.recompAt = Math.trunc(dur / 4); e.chunkLen = Math.trunc(rate / 4); }
    else if (Math.trunc(dur / 20) <= prev) { e.recompAt = Math.trunc(dur / 10); e.chunkLen = Math.trunc(rate / 6); }
    else { e.recompAt = Math.trunc(dur / 20); e.chunkLen = Math.trunc(rate / 9); }
  } else { e.recompAt = dur; e.chunkLen = rate * 5; }
  if (e.half) e.chunkLen = Math.trunc(e.recompAt / 2);
  if (e.chunkLen < 1) e.chunkLen = 1;
}
function adsrNextChunk(e, rem) {
  switch (e.stage) {
    case 1: {
      var a = e.aS > 0 ? e.aS : 1;
      var step = a;
      if (!e.half) {
        var l = e.target < 0 ? -e.target : e.target;
        var q = Math.trunc(a / (l > 1 ? l : 1));
        step = q > 0 ? q : 1;
      }
      var c = a - e.prog;
      if (step < c) c = step;
      if (rem < c) c = rem;
      return c > 0 ? c : 1;
    }
    case 2: {
      var r2 = e.dS - e.prog;
      var c2 = e.chunkLen < r2 ? e.chunkLen : r2;
      return c2 < rem ? c2 : rem;
    }
    case 4: {
      var r4 = e.rS - e.prog;
      var c4 = e.chunkLen < r4 ? e.chunkLen : r4;
      return c4 < rem ? c4 : rem;
    }
    default: return rem;
  }
}
function adsrAdvance(e, len) {
  var fr = Math.fround;
  while (len > 0) {
    switch (e.stage) {
      case 1: {
        var a = e.aS > 0 ? e.aS : 1;
        var need = a - e.prog;
        if (len >= need) {
          e.prog = 0; e.stage = 2; e.cur = e.target; e.recompAt = 0;
          adsrRecompute(e); len -= need;
        } else {
          e.prog += len;
          var lvl = Math.trunc((e.prog * e.target) / a);
          if (lvl > e.target) lvl = e.target;
          e.cur = lvl; len = 0;
        }
        break;
      }
      case 2:
      case 4: {
        var total = e.stage === 2 ? e.dS : e.rS;
        var start = e.stage === 2 ? e.target : e.off;
        var target = e.stage === 2 ? e.susLevel : 0;
        var delta = start - target;
        var mode = e.stage === 2 ? e.dMode : e.rMode;
        var n = len;
        if (n > e.chunkLen) n = e.chunkLen;
        var remN = total - e.prog;
        if (n > remN) n = remN;
        if (n <= 0) {
          if (e.stage === 2) { e.stage = 3; e.cur = e.susLevel; }
          else { e.stage = 0; e.cur = 0; }
          len = 0; break;
        }
        var end = e.prog + n;
        var f = fr(1.0 / total);
        if (mode === 1) {
          var lvl1 = start - Math.trunc(fr(fr(fr(end) * fr(delta)) * f));
          if (lvl1 < target) lvl1 = target;
          e.cur = lvl1;
        } else {
          var r = fr(fr(total - end) * f);
          e.cur = Math.trunc(fr(fr(fr(Math.exp((r - 1) * 8)) * r) * delta)) + target;
        }
        e.prog = end;
        len -= n;
        var done = !(e.prog < total && target < e.cur);
        if (!done && e.half === 1 && e.stage === 4 && mode === 0 &&
            e.prog >= Math.trunc(fr(total) * 0.9)) done = true;
        if (done) {
          if (e.stage === 2) { e.stage = 3; e.cur = e.susLevel; }
          else { e.stage = 0; e.cur = 0; }
          len = 0; break;
        }
        if (e.prog >= e.recompAt) adsrRecompute(e);
        break;
      }
      case 3: e.cur = e.susLevel; len = 0; break;
      default: e.cur = 0; len = 0; break;
    }
  }
  return e.cur;
}

function mkModEnv() {  return { stage: 0, prog: 0, cur: 0, target: 0, aS: 0, dS: 0,
           recompAt: 0, chunkLen: 1, chRem: 0, lvl: 0, lin: 0, sign: 1 };
}
function modEnvReset(mv) {
  mv.stage = 0; mv.prog = 0; mv.cur = 0; mv.recompAt = 0;
  mv.chunkLen = 1; mv.chRem = 0; mv.lvl = 0;
}
/* FUN_18000c930 (note-on) after reset: attack from 0 */
function modEnvNoteOn(mv, on, aS, dS, target, lin, sign) {
  modEnvReset(mv);
  mv.aS = aS; mv.dS = dS; mv.target = target; mv.lin = lin; mv.sign = sign;
  if (on) { mv.stage = 1; mv.prog = 0; mv.recompAt = 0; }
}
function modEnvRecompute(mv) {
  var dur = mv.dS, delta = mv.target;   // mod env decays toward 0 (sustain)
  if (dur < 1) dur = 1;
  if (delta < 1) delta = 1;
  var rate = (dur / delta) | 0;
  if (mv.lin) { mv.chunkLen = rate > 1 ? rate : 1; mv.recompAt = dur; return; }
  var prev = mv.recompAt;
  if (prev < ((dur / 2) | 0)) {
    if (((dur / 3) | 0) <= prev) { mv.recompAt = (dur / 2) | 0; mv.chunkLen = rate * 2; }
    else if (((dur / 4) | 0) <= prev) { mv.recompAt = (dur / 3) | 0; mv.chunkLen = rate; }
    else if (((dur / 10) | 0) <= prev) { mv.recompAt = (dur / 4) | 0; mv.chunkLen = (rate / 4) | 0; }
    else if (((dur / 20) | 0) <= prev) { mv.recompAt = (dur / 10) | 0; mv.chunkLen = (rate / 6) | 0; }
    else { mv.recompAt = (dur / 20) | 0; mv.chunkLen = (rate / 9) | 0; }
  } else { mv.recompAt = dur; mv.chunkLen = rate * 5; }
  if (mv.chunkLen < 1) mv.chunkLen = 1;
}
function modEnvNextChunk(mv, rem) {
  if (mv.stage === 1) {
    var a = mv.aS > 0 ? mv.aS : 1;
    var l = mv.target > 0 ? mv.target : 1;
    var q = (a / l) | 0;
    var step = q > 0 ? q : 1;
    var c = a - mv.prog;
    if (step < c) c = step;
    if (rem < c) c = rem;
    return c > 0 ? c : 1;
  }
  if (mv.stage === 2) {
    var r = mv.dS - mv.prog;
    var c2 = mv.chunkLen < r ? mv.chunkLen : r;
    return c2 < rem ? c2 : rem;
  }
  return rem;
}
function modEnvAdvance(mv, len) {
  while (len > 0) {
    if (mv.stage === 1) {
      var a = mv.aS > 0 ? mv.aS : 1;
      var need = a - mv.prog;
      if (len >= need) {
        mv.prog = 0; mv.stage = 2; mv.cur = mv.target;
        mv.recompAt = 0; modEnvRecompute(mv); len -= need;
      } else {
        mv.prog += len;
        var lvl = Math.trunc((mv.prog * mv.target) / a);
        if (lvl > mv.target) lvl = mv.target;
        mv.cur = lvl; len = 0;
      }
    } else if (mv.stage === 2) {
      var total = mv.dS, start = mv.target, delta = mv.target - 0;
      var n = len;
      if (n > mv.chunkLen) n = mv.chunkLen;
      var rem = total - mv.prog;
      if (n > rem) n = rem;
      if (n <= 0) { mv.stage = 3; mv.cur = 0; len = 0; break; }
      var end = mv.prog + n;
      var lvl2;
      if (mv.lin) {
        lvl2 = start - Math.trunc((end * delta) / total);
        if (lvl2 < 0) lvl2 = 0;
      } else {
        var r = (total - end) / total;
        lvl2 = Math.trunc(Math.exp((r - 1) * 8) * r * delta);
      }
      mv.cur = lvl2; mv.prog = end; len -= n;
      if (!(mv.prog < total && 0 < mv.cur)) { mv.stage = 3; mv.cur = 0; len = 0; break; }
      if (mv.prog >= mv.recompAt) modEnvRecompute(mv);
    } else { mv.cur = 0; len = 0; break; }
  }
  return mv.cur;
}
/* frequency slew + phase rescale (FUN_180014ff0): 1000 Hz/s glide */
function lfoFreqSlew(st, n) {
  var cur = st.freqCur, tgt = st.freqTarget;
  if (cur === tgt) return;
  var step = Math.fround(n / (st.sampleRate * 0.001));
  if (tgt <= cur) { cur -= step; if (tgt > cur) cur = tgt; }
  else { cur += step; if (cur > tgt) cur = tgt; }
  var oldPeriod = st.period;
  st.freqCur = cur;
  st.period = (st.sampleRate / cur) | 0;
  if (oldPeriod > 0) st.phase = ((st.period * st.phase) / oldPeriod) | 0;
}
/* the 6 integer waveforms (FUN_180014d10); returns v in [mn,mx] at phase p.
 * LFO_SEGLEN = core's *outSegLen: samples until this waveform segment ends
 * (segEnd - p, clamped up to minSegment; -1 when hi == lo). segment_at /
 * read_at (lfo.h) cut the CONTROL_TICK grid at these boundaries so a square
 * wave steps exactly at the device tick grid, not at block boundaries. */
var LFO_SEGLEN = 0;
function lfoWaveform(wave, P, p, lo, hi, rndCur, rndNext, minSegment) {
  if (hi === lo) { LFO_SEGLEN = -1; return hi; }
  var mx = hi, mn = lo, flip = hi < lo;
  if (flip) { mx = lo; mn = hi; }
  var v = mn, segEnd = P;
  switch (wave) {
    case 0: { var span = (mx - mn) + 1;
      if (span < P) { v = mx - (span * p) / P; segEnd = (((mx - v) + 1) * P - mn + mx) / span; }
      else { v = mx - ((mx - mn) * p) / (P - 1); segEnd = p + 1; }
      break; }
    case 1: { var half = P / 2, sp = mx - mn;
      if (p < half) { v = mn + (sp * p) / half;
        segEnd = (sp < P) ? ((((v - mn) + 1) * half - mn - 1 + mx) / sp) : (p + 1); }
      else { var rem = P - half; v = mx - (sp * (p - half)) / rem;
        segEnd = (sp < rem) ? ((((mx - v) + 1) * rem - mn - 1 + mx) / sp + half) : ((p - half) + 1 + half); }
      break; }
    case 2: v = (p < P / 2) ? mx : mn; segEnd = (p < P / 2) ? P / 2 : P; break;
    case 3: v = rndCur; segEnd = P; break;
    case 4: { var a = rndNext, b = rndCur;
      if (a === b) { v = b; segEnd = P; }
      else { if (a <= b) { flip = !flip; mx = b; mn = a; } else { mx = a; mn = b; }
        var s2 = (mx - mn) + 1;
        if (s2 < P) { v = mx - (s2 * p) / P; segEnd = (((mx - v) + 1) * P - mn + mx) / s2; }
        else { v = mx - ((mx - mn) * p) / (P - 1); segEnd = p + 1; } }
      break; }
    case 5: { var T = lfoWave5Table(); var idx = (((p << 11) >>> 0) / (P > 0 ? P : 1)) | 0;
      v = (Math.fround(Math.fround(mx - mn) * T[idx] + Math.fround(mx + mn))) | 0; v = v / 2;
      segEnd = p + (minSegment - p % minSegment);
      break; }
    default: break;
  }
  if (flip) v = mn + (mx - v);
  if (segEnd > P) segEnd = P;
  var segLen = segEnd - p;
  if (segLen < minSegment) segLen = minSegment;
  LFO_SEGLEN = segLen;
  return v | 0;
}
/* segment_at (lfo.h): samples until this LFO's next segment boundary when
 * read at (phase + off) mod period; huge when it imposes no boundary. */
function lfoSegRemaining(st, off) {
  if (!st.onOff || st.period <= 0) return 0x7fffffff;
  var p = st.phase + off;
  if (st.period <= p) p %= st.period;
  lfoWaveform(st.wave, st.period, p, st.lo, st.hi, st.rndCur, st.rndNext, st.minSegment);
  if (LFO_SEGLEN <= 0) return 0x7fffffff;
  return LFO_SEGLEN;
}
/* lfo_tick (FUN_180014f60 + FUN_180014ff0): advance phase by n, S&H re-seed, slew */
function lfoTick(st, n) {
  /* P (staged law): plain close_chunk phase close-out — the S&H/
   * random-glide re-seed moved to the voice tick loop (core lfo_tick
   * advances per 32-chunk inside the render pass). */
  st.phase += n;
  if (st.period > 0 && st.phase >= st.period) st.phase %= st.period;
  lfoFreqSlew(st, n);
  return lfoWaveform(st.wave, st.period, st.phase, st.lo, st.hi, st.rndCur, st.rndNext, st.minSegment);
}
/* FUN_180015450 (params 42/47): set the wave; waves 3/4 seed rndNext =
 * (lo+hi)/2 and draw rndCur from the shared CRT rand() stream — this is the
 * draw that happens once per patch load (the device dispatches 42/47 when it
 * loads a bank sound). */
/* panel step (params.json numbers order [0,1,5,2,3,4]) -> core wave enum */
var LFO_TYPE = [0, 1, 5, 2, 3, 4];
function lfoSetWave(st, wave) {
  st.wave = wave;
  if (((wave - 3) >>> 0) < 2) {
    st.rndNext = ((st.lo + st.hi) / 2) | 0;
    st.rndCur = lfoDrawSh(st);
  }
}
/* FUN_1800152e0: key-sync reset (phase 0); waves 3/4 carry rndCur into rndNext
 * and redraw from the shared stream. The device calls it only from a LIVE
 * note-on that makes the held-key count 1 (never for arp-emitted notes). */
function lfoKeySync(st) {
  st.phase = 0;
  if (((st.wave - 3) >>> 0) < 2) {
    st.rndNext = st.rndCur;
    st.rndCur = lfoDrawSh(st);
  }
}
function lfoWaveAt(st) {
  return lfoWaveform(st.wave, st.period, st.phase, st.lo, st.hi, st.rndCur, st.rndNext, st.minSegment);
}

/* headless-safe base so the file can also be unit-tested under Node */
var Synth1Base = (typeof AudioWorkletProcessor !== 'undefined')
  ? AudioWorkletProcessor
  : function () {};

/* I (staged law): init-sound byte table (factory program-0 int displays;
 * reports/object_ctor_defaults_full.md) — device boots by replaying these
 * through set_param. Generated from install/base_params.txt. */
var INIT_SOUND_BYTES = {
  0: 2, 1: 1, 2: 0, 4: 1, 6: 0, 7: 0, 8: 64, 9: 0,
  10: 0, 11: 0, 12: 0, 13: 0, 14: 1, 15: 0, 16: 64, 17: 32,
  18: 64, 19: 81, 20: 14, 21: 65, 22: 64, 23: 0, 24: 1, 25: 64,
  26: 64, 27: 107, 28: 64, 29: 107, 30: 64, 31: 1, 32: 0, 34: 64,
  36: 40, 38: 0, 39: 0, 40: 12, 41: 2, 42: 1, 43: 64, 44: 0,
  45: 0, 46: 5, 47: 1, 48: 64, 49: 64, 53: 64, 56: 40, 57: 1,
  58: 1, 59: 0, 60: 64, 63: 64, 64: 2, 65: 1, 66: 1, 67: 0,
  68: 0, 69: 0, 70: 0, 71: 0, 73: 0, 74: 0, 75: 22, 76: 0,
  77: 0, 78: 0, 79: 64, 80: 64, 81: 64, 82: 0, 84: 0, 85: 0,
  86: 45057, 87: 44, 88: 45057, 89: 43, 91: 0, 92: 0, 93: 2, 94: 16,
  95: 0, 96: 1, 97: 1, 98: 64, 99: 0, 100: 0, 101: 0, 102: 0,
  103: 0, 104: 0, 105: 0, 106: 0, 107: 0, 108: 0, 109: 0, 110: 0,
  111: 0, 112: 0, 113: 0, 114: 0, 115: 0, 116: 0, 117: 0, 118: 0,
  119: 0, 120: 0, 121: 0, 122: 0, 123: 0, 124: 0, 125: 0, 126: 0,
  127: 0,
};
var INIT_SOUND_IDS = Object.keys(INIT_SOUND_BYTES).map(Number);

class Synth1Processor extends Synth1Base {
  constructor() {
    super();
    this.params = {};
    this.voices = [];
    /* spec_phase Branch C reseed is PER VOICE (voice ctor + patch-load loop,
     * spec §2): each voice object carries its own `reseed` flag. */
    this.maxVoices = 32;
    this.sustain = false;
    this.pb = 0;          // -8192..8191
    this.mod = 0;         // 0..127
    this.volScale = 1;    // host volume knob
    this.time = 0;        // seconds of rendered audio
    this.absPos = 0;      // absolute sample position (control-tick grid base)
    this.lfoState = [mkLfo(44100), mkLfo(44100)];
    this._seq = 0;
    crtSrand(1);   /* engine.cpp prepare: rng::crt_srand(1) — the CRT stream
                    * starts at _holdrand = 1 and is never srand'd again. */
    /* CArpeggiator state (spec_lfo_fx.md §7.1 ctor FUN_180001240):
     * tempo 120, stepLen 22050, octave span 2 (octaves 1), gate 0.5,
     * beatDiv 24, mode 1, off. held = keys+0xc 128-slot array. */
    this.arp = {
      sr: 44100, tempo: 120.0, stepLen: 22050, octaves: 1, gate: 0.5,
      beatDiv: 24, beatIdx: 7, pos: 0, gateOn: true, dir: 0, octIdx: 0,
      lastIdx: -1, curNote: -1, velocity: 127, mode: 1, enabled: false,
      held: new Uint8Array(128)
    };
    this.arpNote = -1;        // engine arp_note (currently sounding arp pitch)
    this.arpGateOffAt = 0;    // sample-in-step of the next gate-off edge
    this._arpKeys = new Int32Array(128);   // scratch for random held-key scan
    /* Live-keyboard state (FUN_180028020 keyboardInfo keys+0xc / +0x20c):
     * the LFO key-sync gate is a LIVE note-on that makes the held-key count 1.
     * Arp-emitted notes go through FUN_1800280b0 (second keyboard) and never
     * touch this count, so they never key-sync. */
    this.liveKeys = new Uint8Array(128);
    this.liveKeyCount = 0;
    /* ---- post-voice FX chain state (allocated once; hot path is allocation-free) ---- */
    this._sr = 44100;
    this.chorus = {
      onOff: 0, mode: 2, baseDelaySec: 0.02, baseDelaySamples: 882, depthParam: 0.5,
      depthSamples: 441, depthNorm: 1, depthStep: 100, feedback: 0, feedbackOn: 0,
      level: 1, dryGain: 1, lfoPeriod: 44100, phaseStep: 2 * Math.sin(Math.PI / 44100),
      oscS0: 0, oscS1: 0.9999, rateHz: 1, writePos: 882, readPos: 0,
      tailBudget: 0, silentFrames: 99999999, delayActive: 1,
      lineL: new Float32Array(CHORUS_LINE_SIZE), lineR: new Float32Array(CHORUS_LINE_SIZE),
      toneL: null, toneR: null
    };
    this.delay = {
      onOff: 0, mode: 0, feedback: 0.7, dry: 1, wet: 1, spread: 0.1, chainMode: true,
      timeSec: 0, timeSamp: 0, rightTap: 0, leftTap: 0, slewing: 0, rightLive: 0, leftLive: 0,
      tailBudget: 1, silentFrames: 99999999, outActive: 0,
      tapSlew: 0, toneType: 0, toneFreq: 0, toneA0: 0, toneA2: 0,
      toneX1L: 0, toneX1R: 0, toneY1L: 0, toneY1R: 0, writePos: 0,
      lineL: new Float32Array(DELAY_LINE_SIZE), lineR: new Float32Array(DELAY_LINE_SIZE),
      toneL: new Float32Array(DELAY_MAX_FRAMES), toneR: new Float32Array(DELAY_MAX_FRAMES)
    };
    this.delayBeatIndex = 0;
    this._pan90 = { gl: 1, gr: 1 };
    /* unison / per-voice pan spread (params 73/84/93): fixed 32-slot pool */
    this.unisonOn = false;
    this.unisonCount = 2;
    this.voicePan = new Float32Array(32);
    /* CEffector (+0x9718, fx/effector.cpp) + CEq (+0x9a98/+0x9b18, fx/eq.cpp):
     * FxChain::process order effector -> eqA -> eqB -> pan -> delay -> chorus;
     * the EQ bands are ALWAYS live (core: the +0x1c gate is ctor-set, param 73
     * writes the non-process +0x20 flag only). */
    this.efOn = 0; this.efType = 0; this.efCtl1 = 0; this.efCtl2 = 0; this.efLevel = 0;
    this.efDist = { curve: 0, drive: 1, level: 0, norm: 1, toneCut: 127, toneA: 1, y1L: 0, y1R: 0 };
    this.efComp = { thrDb: -20, thrLin: 0.1, atk: 0.2, rel: 0.2, makeup: 1, ctl2raw: 0, envL: 0, envR: 0 };
    this.efRm = { freq: 1000, k: 0, level: 0, s0: 1, s1: 0 };
    this.efDec = { period: 1, mask: -2, mix: 0, cnt: 0, heldL: 0, heldR: 0 };
    this.efPh = { nPairs: 1, fb: 0, rate: 0.01, g: 0.02, gStep: 1, frozen: false,
                 s: new Float32Array(24), accL: 0, accR: 0 };
    this.eqA = this.mkEq(0);
    this.eqB = this.mkEq(0);
    this._rrCursor = -1;   // FUN_180036f30 rr cursor (first allocation = slot 0)
    this._monoHeld = [];   // mono/legato held-note stack
    /* I (staged law): boot the param store at the init-sound bytes (the
     * same setParam values present params use); present params overwrite. */
    for (var _bi = 0; _bi < INIT_SOUND_IDS.length; _bi++) {
      this.params[INIT_SOUND_IDS[_bi]] = INIT_SOUND_BYTES[INIT_SOUND_IDS[_bi]];
    }
    /* plugin defaults for params absent from a .sy1 (engine prepare, base_params):
     * 82 delay type 0, 83 spread 66 (+0.1 ms), 98 tone 64 (off), 90 pan centre,
     * 84 spread 64 (0), 93 count 9 (N = 2), 73 unison off. */
    this.chorusSetSampleRate(44100);
    this.delaySetSampleRate(44100);
    this.effectorSetSampleRate(44100);
    this.fxParam(82, 0); this.fxParam(83, 66); this.fxParam(98, 64); this.fxParam(90, 64);
    this.params[84] = 64; this.params[93] = 9;
    this.recomputeVoicePans();
    if (this.port) this.port.onmessage = (ev) => this.handle(ev.data);
  }

  P(id, dflt) {
    var v = this.params[id];
    return (v === undefined || v === null) ? dflt : v;
  }

  handle(m) {
    if (!m || !m.t) return;
    switch (m.t) {
      case 'p':
        this.params[m.id] = m.v;
        this.arpParam(m.id, m.v);
        this.lfoParam(m.id, m.v);
        this.fxParam(m.id, this.rawBand(m.id, m.v));
        if (Number(m.id) === 91) this.armPhaseReseedAll();
        if (Number(m.id) === 45) this.fmKnobChange45();
        break;
      case 'ps':
        for (var k in m.m) this.params[k] = m.m[k];
        var ids = Object.keys(m.m).map(Number).sort(function (x, y) { return x - y; });
        for (var ki = 0; ki < ids.length; ki++) {
          var id2 = ids[ki];
          this.arpParam(id2, m.m[id2]);
          this.lfoParam(id2, m.m[id2]);
          this.fxParam(id2, this.rawBand(id2, m.m[id2]));
        }
        /* spec_phase §2 FUN_18003e390/FUN_18003cde0: the param-91 dispatch
         * (every patch load dispatches it, default 0) sets the reseed-once
         * flag (+0x1bc) of ALL voices to (param91 <= 0) — each voice's next
         * band-0 note-on consumes its 10 PHASE_LCG draws again. */
        this.armPhaseReseedAll();
        if (m.m && ('45' in m.m || 45 in m.m)) this.fmKnobChange45();
        break;
      case 'on': this.handleNoteOn(m.note, m.vel === undefined ? 100 : m.vel); break;
      case 'off': this.handleNoteOff(m.note); break;
      case 'pb': this.pb = clamp(m.v, -8192, 8191); break;
      case 'sus':
        this.sustain = !!m.on;
        if (!this.sustain) this.releaseHeld();
        break;
      case 'mod': this.mod = clamp(m.v, 0, 127); break;
      case 'vol': this.volScale = clamp(m.v, 0, 1.5); break;
      case 'tempo': this.arpSetTempo(clamp(Number(m.v), 1, 400)); break;
      case 'panic':
        this.voices.forEach(v => { v.env = 4; });
        this.arpNote = -1;
        this.liveKeys.fill(0); this.liveKeyCount = 0;
        break;
    }
  }

  /* Mod-env trigger (core Voice::note_on → mod_env.reset()+note_on(),
   * spec_env.md §2.4/§5): AD, dest-scaled integer target (voice.h
   * MOD_ENV_SCALE_PITCH 640 / _FM 512 / _PW 128 × |amount|), dest 1 =
   * LINEAR decay, others exponential. */
  /* Core Voice::note_on env law (voice.cpp): CVca (half-chunks) + CVcf
   * (full chunks) note_on with the band-derived times; CVcf target =
   * (int)(1024·|headroom-clamped amount|), sign kept for the stair-step.
   * Legato attack progress resumes at (a·cur)/target (adsr.h note_on). */
  _envTrigger(v) {
    var sr = (typeof sampleRate === 'number' && sampleRate > 0) ? sampleRate : 44100;
    var a = this.adsr();
    var ae = v.ae || (v.ae = mkAdsr(2048, true));
    adsrTimes(ae, Math.trunc(sr * a.a), Math.trunc(sr * a.d), Math.trunc(sr * a.r));
    adsrSustain(ae, a.s);
    adsrNoteOn(ae);
    var fa = this.filterAdsr();
    var fe = v.fe || (v.fe = mkAdsr(1024, false));
    adsrTimes(fe, Math.trunc(sr * fa.a), Math.trunc(sr * fa.d), Math.trunc(sr * fa.r));
    adsrSustain(fe, fa.s);
    var i0 = this._i0 !== undefined ? this._i0
      : clamp(Math.floor(clamp(this.P(19, 64), 0, 127) * 1024 / 127), 0, 1023);
    var iKey = keytrackIndex(i0, v.note, this._amt22 !== undefined ? this._amt22
      : clamp(this.P(22, 0), 0, 127) / 127);
    var amt21j = this._amt21 !== undefined ? this._amt21
      : filterAmount(clamp(this.P(21, 63), 0, 127));
    /* J (staged law): filter velocity switch (param 24) scales the FE amount
     * by CVcf+0xc0/127 before the headroom clamp (voice.cpp:156-158). */
    if (clamp(this.P(24, 0), 0, 127) !== 0)
      amt21j = filterVelScale127(v.vel === undefined ? 127 : v.vel) * amt21j * (1 / 127);
    var amt = envHeadroom(i0, iKey, amt21j);
    adsrAmount(fe, Math.abs(amt));
    adsrNoteOn(fe);
    v.env = 0; v.eg = 0; v.aprog = 0; v.offLevel = 0;
    v.fenv = 0; v.feg = 0;
  }

  _modEnvTrigger(v) {
    var mv = v.mv || (v.mv = mkModEnv());
    var sr = (typeof sampleRate === 'number' && sampleRate > 0) ? sampleRate : 44100;
    var dest = clamp(this.P(71, 0), 0, 7);   /* Q: lfo.h DEST enum */
    var amt = modEnvAmount(clamp(this.P(11, 64), 0, 127));
    modEnvNoteOn(mv, this.P(10, 0) !== 0,
      Math.trunc(sr * ampAttackSec(clamp(this.P(12, 0), 0, 127))),
      Math.trunc(sr * ampDecaySec(clamp(this.P(13, 0), 0, 127))),
      Math.trunc(((dest === 1 || dest === 2) ? 640 : dest === 6 ? 512
                  : dest === 5 ? 128 : 0) * Math.abs(amt)),
      dest === 6 ? 1 : 0, amt < 0 ? -1 : 1);
  }

  /* FM-amount knob (param 45, FUN_18003e050): CVco+0xa0 = raw band,
   * +0xb4 (lastTarget) = −1 forces the state machine on the next target
   * check, +0xc0 (blockCur) = sr/10 arms a 100 ms ramp for the FM-target
   * change the knob produces. */
  fmKnobChange45() {
    var sr = (typeof sampleRate === 'number' && sampleRate > 0) ? sampleRate : 44100;
    var bc = (sr / 10) | 0;
    for (var i = 0; i < this.voices.length; i++) {
      var fm = this.voices[i].fm || (this.voices[i].fm = mkFmRamp());
      fm.lastTarget = -1;
      fm.blockCur = bc;
    }
  }

  masterGain() { return 0.825370 * this.volScale; }   // master-volume tail (param 0xfe default raw 64)
  filterFreq() { return 25 * Math.pow(16000 / 25, clamp(this.P(19, 64), 0, 127) / 127); }
  filterQ() { return 0.5 + 15 * clamp(this.P(20, 10), 0, 127) / 127; }
  adsr() {
    return {
      a: ampAttackSec(clamp(this.P(25, 55), 0, 127)),
      d: ampDecaySec(clamp(this.P(26, 28), 0, 127)),
      s: ampSustainRatio(clamp(this.P(27, 127), 0, 127)),
      r: ampReleaseSec(clamp(this.P(28, 64), 0, 127))
    };
  }

  filterAdsr() {
    return {
      a: ampAttackSec(clamp(this.P(15, 0), 0, 127)),
      d: ampDecaySec(clamp(this.P(16, 64), 0, 127)),
      s: clamp(this.P(17, 0), 0, 127) / 127,
      r: ampReleaseSec(clamp(this.P(18, 64), 0, 127))
    };
  }
  filterAmt() {
    return filterAmount(clamp(this.P(21, 63), 0, 127));
  }

  pbCents() {
    var range = clamp(this.P(40, 2), 0, 24);
    return this.pb / 8192 * range * 100;
  }

  /* law helpers exposed for unit tests (same functions the render loop uses) */
  rawBand(id, k) { return rawBand(id, k); }
  fineCents(b) { return fineCents(b); }
  filterAmount(b) { return filterAmount(b); }
  modEnvAmount(b) { return modEnvAmount(b); }
  mixGains(mix, subAmp) { return mixGains(mix, subAmp); }
  pulseDutyIndex(pw, pwMod) { return pulseDutyIndex(pw, pwMod); }
  fcOfIndex(i) { return fcOfIndex(i); }
  keytrackIndex(i0, note, amt) { return keytrackIndex(i0, note, amt); }
  envHeadroom(i0, iKey, amt) { return envHeadroom(i0, iKey, amt); }
  mirrorFoldAdd(i, m) { return mirrorFoldAdd(i, m); }
  lfoRange(dest, depth) { return lfoRange(dest, depth); }
  fmDepthFromGate(amtBand, gate) { return fmDepthFromGate(amtBand, gate); }

  /* base oscillator frequencies (spec_osc.md 4.1, FUN_18003bb00/3bba0) with
   * the per-voice unison detune cents added to fine12 (voice.cpp
   * update_base_pitch: pitch_cents = fine12 + unison_pitch_cents). */
  oscFreqs(note, detuneCents) {
    var shift = rawBand(9, clamp(this.P(9, 24), 0, 48));
    var n = clamp(note + shift, 0, 127);
    var fine12 = fineCents(rawBand(72, clamp(this.P(72, 62), 0, 123))) + (detuneCents || 0);
    var f1 = 440 * Math.pow(2, (n - 69) / 12) * Math.pow(2, fine12 / 1200);
    var raw2 = rawBand(2, clamp(this.P(2, 60), 0, 120));
    var oct2 = (Math.floor(raw2 * 120 / 127) - 60) / 12;
    var fine2 = fineCents(rawBand(3, clamp(this.P(3, 62), 0, 123)));
    var f2;
    if (this.P(4, 1) !== 0) {
      f2 = f1 * Math.pow(2, oct2 + fine2 / 1200);
    } else {
      f2 = 220 * Math.pow(2, (fine12 + fine2) / 1200 + oct2);
    }
    return { f1: f1, f2: f2 };
  }

  /* LFO destination routing (FUN_18003dbe0): dest 1 -> osc2 only,
   * dest 2 -> both oscs, dest 3 -> filter (mirror-folded in CVcf), 4 -> amp,
   * 5 -> pulse width. The integer LFO value is read at the CURRENT phase. */
  lfoRoute(li, mod, off) {
    var st = this.lfoState[li];
    if (!st.onOff || !st.dest) return;
    var p = st.phase + (off || 0);
    if (st.period > 0 && st.period <= p) p %= st.period;
    var v = lfoWaveform(st.wave, st.period, p, st.lo, st.hi,
                        st.rndCur, st.rndNext, st.minSegment);
    switch (st.dest) {
       case 1: mod.pitch2 += v; break;
       case 2: mod.pitch += v; break;
       case 3: mod.cutoff += v; break;
       case 4: mod.amp += v; break;
       case 5: mod.pw += v; break;
       case 6: mod.fm += v; break;
       case 7: mod.pan += v; break;
       default: break;
     }
   }

  /* FUN_180028fe0 LFO cases (41-44/46-49/57/58/67-70), dispatched per param in
   * patch order. Params 42/47 go through FUN_180015450, which draws the S&H
   * value from the shared CRT rand() stream: the device dispatches them when it
   * loads a bank sound (001 at construction), so a patch load draws each
   * wave-3/4 LFO exactly once — the patch-load S&H parity. */
  lfoParam(id, band) {
    var st = this.lfoState[(id >= 46 && id <= 49) || id === 58 || id === 69 || id === 70 ? 1 : 0];
    switch (id) {
      case 41: st.dest = band; lfoDepthToRange(st); break;
      /* O (staged law, §G ruling): .sy1 band IS the engine wave enum
       * (LFO_TYPE is the panel step -> enum map, not a band map). */
      case 42: lfoSetWave(st, clamp(band, 0, 5)); break;
      case 43: st.speed = band; lfoSpeedToHz(st, this.arp.tempo); break;
      case 44: st.depth = band; lfoDepthToRange(st); break;
      case 46: st.dest = band; lfoDepthToRange(st); break;
      case 47: lfoSetWave(st, clamp(band, 0, 5)); break;
      case 48: st.speed = band; lfoSpeedToHz(st, this.arp.tempo); break;
      case 49: st.depth = band; lfoDepthToRange(st); break;
      case 57: case 58: st.onOff = band !== 0 ? 1 : 0; break;
      case 67: case 69: st.tempoSync = band !== 0 ? 1 : 0; lfoSpeedToHz(st, this.arp.tempo); break;
      case 68: case 70: st.keySync = band !== 0 ? 1 : 0; break;
      default: break;
    }
  }

  /* sync one LFO state from the current params (engine.cpp cases 41-49/57/58/67-70) */
  lfoSync(li) {
    var st = this.lfoState[li];
    var b = li ? 46 : 41;
    var on = this.P(li ? 58 : 57, 0) !== 0 ? 1 : 0;
    var dest = clamp(this.P(b, 0), 0, 7);
    /* O (staged law): raw band = engine wave enum (§G ruling). */
    var wave = clamp(this.P(b + 1, 0), 0, 5);
    var speed = clamp(this.P(b + 2, 0), 0, 127);
    var depth = clamp(this.P(b + 3, 0), 0, 127);
    var ts = this.P(li ? 69 : 67, 0) !== 0 ? 1 : 0;
    var ks = this.P(li ? 70 : 68, 0) !== 0 ? 1 : 0;
    if (st.sampleRate !== this._sr) { st.sampleRate = this._sr; st.period = (st.sampleRate / st.freqCur) | 0; }
    st.onOff = on; st.keySync = ks;
    if (st.dest !== dest) { st.dest = dest; lfoDepthToRange(st); }
    if (st.depth !== depth) { st.depth = depth; lfoDepthToRange(st); }
    if (st.speed !== speed || st.tempoSync !== ts) { st.speed = speed; st.tempoSync = ts; lfoSpeedToHz(st, this.arp.tempo); }
    /* FUN_180015450: a wave change seeds the S&H pair from the shared stream
     * (the dispatch path already did it for patch loads; this covers direct
     * param writes). */
    if (st.wave !== wave) lfoSetWave(st, wave);
  }


  /* FUN_18003e390 (dispatcher case 0x5b): the param-91 setter is applied to
   * EVERY voice (control-rate dispatch, core engine.cpp dispatch_param):
   * CVco+0x1bc = (param91 <= 0). */
  armPhaseReseedAll() {
    var armed = (clamp(this.P(91, 0), 0, 126) | 0) <= 0 ? 1 : 0;
    for (var i = 0; i < this.voices.length; i++) this.voices[i].reseed = armed;
  }

  /* voice.cpp FUN_18003e600 (+ engine.cpp note_on_live skip-6 prime) applied
   * to ONE pool voice: returns [ph1, ph2] to write into the voice, or null
   * for FREE-RUN (band 0, reseed flag clear — phases untouched, no draws).
   * `v` is the existing voice, null for a never-played slot (its first note).
   * vIdx/vCount = unison voice index/count, uPhase = param 92 band. */
  _phaseForVoice(v, band, playMode, vIdx, vCount, uPhase) {
    if (band > 0) {
      /* Branch A — immobilize: EVERY note-on re-seeds from the fixed T
       * table (no LCG draws). Core voice.cpp: osc1 = 0,
       * osc2 = (int)((float)((float)(band−1)·(1/126f))·2^26) & 0x7ffffff;
       * spec_phase §4 unison block (count>1, param92>0): +
       * (int)(U·T[10·vIdx+j]·2^27) per osc, U = param92·(1/127f). */
      var ph1 = 0;
      var ph2 = (Math.fround(Math.fround(band - 1) * PHASE_INV126) * 67108864) | 0;
      if (vCount > 1 && uPhase > 0) {
        var u = Math.fround(uPhase * PHASE_INV127);
        ph1 = (ph1 + (Math.fround(Math.fround(u * PHASE_T[(10 * vIdx) & 511]) * 134217728) | 0)) & 0x7ffffff;
        ph2 = (ph2 + (Math.fround(Math.fround(u * PHASE_T[(10 * vIdx + 1) & 511]) * 134217728) | 0)) & 0x7ffffff;
      }
      if (v) v.reseed = 0;
      return [ph1 >>> 0, ph2 >>> 0];
    }
    /* Band 0: Branch C per-voice first note (ctor/patch-load armed),
     * else Branch B free-run. */
    if (v === null || v.reseed) {
      /* v100 2026-10-08: the skip-6 note_on_live prime was WRONG (engine.cpp
       * removed) — PHASE_LCG state is 1 at the first note-on for every patch;
       * the first Branch-C note-on consumes exactly draws 1..10. */
      var a = nextRandomPhase();
      var b = nextRandomPhase() & 0x7ffffff;
      for (var d = 0; d < 8; d++) nextRandomPhase();   /* detune-tap slots */
      if (v) v.reseed = 0;
      return [a >>> 0, b >>> 0];
    }
    return null;
  }

  noteOn(note, vel) {
    note = Math.round(note);
    if (note < 0 || note > 127) return;
    /* key-sync is NOT done here: arp-emitted notes reach noteOn through
     * arpStepBoundary (FUN_1800280b0) and must not key-sync. The live-keyboard
     * gate lives in handleNoteOn (FUN_180028020). */
    /* play modes (voice_allocator.cpp §7): 0 poly (round-robin over the
     * param-94 pool, FUN_180036f30), 1 mono (slot 0, env retriggered every
     * note-on, FUN_180036930), 2 legato (slot 0, pitch change without
     * retrigger while a note is gate-held). */
    var playMode = clamp(this.P(38, 0) | 0, 0, 2);
    var pool = clamp(this.P(94, 16) | 0, 1, this.maxVoices);
    var stack = this._monoHeld || (this._monoHeld = []);
    if (playMode === 0) {
      /* F (32-bit law, FUN_10030e40): poly note-on on a pitch with an
       * active voice RELEASES the old voice (gate clear, env release) so the
       * note allocates a FRESH voice (retrigger), not a sustaining overlap. */
      for (var ri = 0; ri < this.voices.length; ri++) {
        var rv = this.voices[ri];
        if (rv.note === note && rv.env < 3) this.startRelease(rv);
      }
    }
    /* F (32-bit law, FUN_10030c20): mono ALWAYS retriggers — the
     * held-note same-pitch early-return is removed. */
    /* unison (param 73 on, param 93 count): a note-on allocates N slots, each
     * carrying its per-voice pan spread (voice_pan_[slot], FUN_180037250). */
    var n = (this.unisonOn && this.unisonCount >= 2) ? this.unisonCount : 1;
    while (this.voices.length + n > this.maxVoices) {
      /* F (32-bit law): steal victim = HEAD of the insertion-ordered
       * active list (array order = insertion order), not min-timestamp. */
      var oldest = this.voices[0];
      this.voices.splice(this.voices.indexOf(oldest), 1);
    }
    var sr = (typeof sampleRate === 'number' && sampleRate > 0) ? sampleRate : 44100;
    var vf = velFactor(clamp(vel, 1, 127), clamp(this.P(30, 22), 0, 127));
    var band = clamp(this.P(91, 0), 0, 126) | 0;
    var uPhase = clamp(this.P(92, 0) | 0, 0, 127);
    if (playMode === 1 || playMode === 2) {
      stack.push(note);
      var mv = null;
      for (var mi = 0; mi < this.voices.length; mi++) {
        if (this.voices[mi].slot === 0 && this.voices[mi].env < 4) { mv = this.voices[mi]; break; }
      }
      if (mv && (playMode === 1 || (playMode === 2 && mv.env < 3))) {
        mv.note = note; mv.vel = vel; mv.order = ++this._seq;
        mv.detuneCents = 0;   // mono/legato: unison n = 1 (note_on_live)
        /* portamento start_glide (voice_allocator.cpp): the glide starts from
         * the CURRENT effective pitch (target + remaining of a running glide,
         * else the new note) and decays exp(-4t)·(1-t) over
         * dur = sr·porta_time, porta_time = exp(2.5(b-1))·b·2.5, b = p39/127.
         * Gate: mono = porta-on (p74==0) or held; legato = same. */
        var pt = clamp(this.P(39, 0), 0, 127);
        var g = mv.porta || (mv.porta = { delta: 0, pos: 0, dur: 0, remaining: 0, target: 0, active: 0 });
        if (pt > 0 && (clamp(this.P(74, 0), 0, 127) === 0 || stack.length >= 1)) {
          var pb = pt / 127;
          var dur = (sr * Math.exp(2.5 * (pb - 1)) * pb * 2.5) | 0;
          var newU = ((note << 7) / 12) | 0;
          var curU = g.active ? g.target + g.remaining : newU;
          var delta = curU - newU;
          g.delta = delta; g.pos = 0; g.dur = dur;
          g.remaining = (delta === 0 || dur === 0) ? 0 : delta;
          g.active = 1; g.target = newU;
        } else { g.active = 0; g.remaining = 0; }
        if (playMode === 1) {
          /* mono: envelope retriggered on every note-on (kPlayMono:
           * trigger_env per note-on, voice_allocator.cpp). The full voice
           * note_on law runs: band >= 1 re-seeds from the T table, band 0
           * FREE-RUNS (the voice's single per-voice seed was spent on its
           * first note — no draws, phases untouched). */
          mv.peak = vf;
          this._envTrigger(mv);
          this._modEnvTrigger(mv);
          fmNoteOnReset(mv.fm || (mv.fm = mkFmRamp()));
          var mph = this._phaseForVoice(mv, band, playMode, 0, 1, uPhase);
          if (mph) { mv.ph1 = mph[0]; mv.ph2 = mph[1]; }
        }
        /* legato (mode 2, gate-held): retarget_note (FUN_1800526e0) — pitch
         * only; the envelope trigger path (FUN_180052740 → phase init) is
         * intentionally NOT run: no draws, phases keep running. */
        return;
      }
      n = 1;
    }
    for (var s = 0; s < n; s++) {
      var slot = (playMode === 1 || playMode === 2) ? 0 : this._allocSlot(pool);
      /* Device voices are persistent per pool slot: the oscillators, the LFSR
       * and the filter core keep running while idle (free-running, spec_phase
       * Branch B). A re-allocated slot REUSES the idle voice object so those
       * states survive the note boundary. Per-voice phase init (voice.cpp
       * FUN_18003e600, see _phaseForVoice): immobilize (91 >= 1) re-seeds
       * every note-on from the T table; band 0 seeds the PHASE_LCG stream on
       * the voice's FIRST note-on only (10 draws) and free-runs after that. */
      var ex = null;
      for (var vi = 0; vi < this.voices.length; vi++) {
        if (this.voices[vi].slot === slot) { ex = this.voices[vi]; break; }
      }
      if (ex) {
        ex.note = note; ex.vel = vel; ex.peak = vf; ex.order = ++this._seq;
        ex.detuneCents = (n > 1) ? unisonSlotPitchCents(s, n, this.P(75, 22), this.P(85, 24)) : 0;
        this._envTrigger(ex);
        ex.held = false;
        this._modEnvTrigger(ex);
        fmNoteOnReset(ex.fm || (ex.fm = mkFmRamp()));
        var eph = this._phaseForVoice(ex, band, playMode, s, n, uPhase);
        if (eph) { ex.ph1 = eph[0]; ex.ph2 = eph[1]; }
        this.initFilter(ex, sr, true);
        continue;
      }
      var nph = this._phaseForVoice(null, band, playMode, s, n, uPhase);
      var ph1 = nph ? nph[0] : 0;
      var ph2 = nph ? nph[1] : 0;
      var newv = {
        note: note, vel: vel, peak: vf, slot: slot, pan: this.voicePan[slot],
        detuneCents: (n > 1) ? unisonSlotPitchCents(s, n, this.P(75, 22), this.P(85, 24)) : 0,
        ph1: ph1, ph2: ph2, lfsr: 10, reseed: false,
        fm: mkFmRamp(),             // FM depth ramp state (core FmRampState)
        mv: mkModEnv(),             // mod env chunk state (core env::ADSR)
        pm2: 0x7fffffff, inc2: 0,   // osc2 pitch-mod gate (FUN_18003b940)
        fmGateP: 0x7fffffff, fmTgt: 0,  // FM gate → target cache
        lev: 0,                      // dynamic leveler env (FUN_18003af70)
        ae: mkAdsr(2048, true), fe: mkAdsr(1024, false),  // env::ADSR chunk state
        gCur: 0, gStep: 0, fltLvl: 0,                    // CVca g-ramp + CVcf chunk level
        env: 0, eg: 0, aprog: 0, offLevel: 0,   // 0 attack 1 decay 2 sustain 3 release 4 done
        fenv: 0, feg: 0,
        held: false, order: ++this._seq
      };
      this.voices.push(newv);
      this._envTrigger(newv);
      this._modEnvTrigger(newv);
      this.initFilter(newv, sr);
    }
  }

  /* Round-robin allocation over the param-94 pool (FUN_180036f30/FUN_180036c00):
   * first slot after the cursor whose gate is free; a voice counts as busy
   * until its envelope has fully finished (env 4) — a releasing voice KEEPS
   * its slot and keeps sounding its tail (the reference renders the tails;
   * reusing a releasing slot audibly truncates them). Only when every slot
   * is busy does allocation steal the oldest. */
  _allocSlot(pool) {
    var cur = this._rrCursor;
    for (var k = 1; k <= pool; k++) {
      var idx = (cur + k) % pool;
      var free = true;
      for (var i = 0; i < this.voices.length; i++) {
        var v = this.voices[i];
        if (v.slot === idx && v.env < 4) { free = false; break; }
      }
      if (free) { this._rrCursor = idx; return idx; }
    }
    /* F (32-bit law, FUN_10030e40): steal = head of the
     * insertion-ordered active list = first voice in array order whose slot
     * is in the pool (NOT the oldest-timestamp voice). */
    var best = null, bi = -1;
    for (var i2 = 0; i2 < this.voices.length; i2++) {
      var v2 = this.voices[i2];
      if (v2.slot < pool) { best = v2; bi = i2; break; }
    }
    var slot = best ? best.slot : ((cur + 1) % pool);
    if (bi >= 0) this.voices.splice(bi, 1);
    this._rrCursor = slot;
    return slot;
  }

  noteOff(note) {
    note = Math.round(note);
    var playMode = clamp(this.P(38, 0) | 0, 0, 2);
    if (playMode === 1 || playMode === 2) {
      /* mono/legato: pop the note from the held stack; fall back to the last
       * held note, release the slot-0 voice only when the stack empties. */
      var stack = this._monoHeld || (this._monoHeld = []);
      for (var i = 0; i < stack.length; i++) {
        if (stack[i] === note) { stack.splice(i, 1); break; }
      }
      var mv = null;
      for (var mi = 0; mi < this.voices.length; mi++) {
        if (this.voices[mi].slot === 0 && this.voices[mi].env < 4) { mv = this.voices[mi]; break; }
      }
      if (!mv) return;
      if (stack.length > 0) { mv.note = stack[stack.length - 1]; return; }
      if (this.sustain) { mv.held = true; return; }
      this.startRelease(mv);
      return;
    }
    this.voices.forEach(v => {
      if (v.note !== note || v.env >= 3) return;
      if (this.sustain) { v.held = true; return; }
      this.startRelease(v);
    });
  }

  startRelease(v) {
    var ae = v.ae, fe = v.fe;
    if (ae) { adsrNoteOff(ae); v.env = 3; v.offLevel = ae.off * (1 / 2048); v.aprog = 0; }
    if (fe) { adsrNoteOff(fe); v.fenv = 3; }
  }

  releaseHeld() {
    this.voices.forEach(v => { if (v.held && v.env < 3) { v.held = false; this.startRelease(v); } });
  }

  /* ---------------- Arpeggiator (spec_lfo_fx.md §7) ----------------
   * State machine ported from core/arp/arpeggiator.cpp. The clock unit is
   * 1/24 of a quarter note; stepLen = (int)(sr·BEAT·60 / (tempo·24)). */
  arpRecompute() {
    var a = this.arp, old = a.stepLen;
    a.stepLen = (a.sr * a.beatDiv * 60) / (a.tempo * 24.0) | 0;
    if (old !== 0) a.pos = (a.pos * a.stepLen / old) | 0;   // §7.2 phase rescale
  }
  arpSetTempo(bpm) { this.arp.tempo = bpm; this.arpRecompute(); }
  arpSetBeatIndex(idx) {
    idx = clamp(idx | 0, 0, 18);
    var a = this.arp;
    if (a.beatDiv !== ARP_BEAT[idx]) { a.beatDiv = ARP_BEAT[idx]; a.beatIdx = idx; this.arpRecompute(); }
  }
  arpSetGate(raw) { this.arp.gate = (raw | 0) / 127.0; }   // FUN_180001f20
  arpSetMode(mode) {                                        // FUN_180002090
    var a = this.arp;
    a.mode = mode; a.pos = 0; a.octIdx = 0; a.gateOn = true;
    a.dir = (mode === 3) ? 1 : 0; a.curNote = -1;
  }
  arpSetOctaves(o) { this.arp.octaves = clamp(o | 0, 0, 3); }   // FUN_18000d2b0
  arpSetEnabled(on) {                                         // FUN_180001ec0
    var a = this.arp;
    a.enabled = on; a.pos = 0; a.octIdx = 0; a.gateOn = true; a.curNote = -1;
  }
  arpParam(id, v) {                                          // engine dispatch_param
    switch (id) {
      case 31: this.arpSetMode(ARP_MODE[clamp(v | 0, 0, 3)]); break;
      case 32: this.arpSetOctaves(v | 0); break;
      case 33: this.arpSetBeatIndex(v | 0); break;
      case 34: this.arpSetGate(clamp(v | 0, 0, 127)); break;
      case 59: {
        var on = (v | 0) !== 0;
        if (!on && this.arp.enabled && this.arpNote !== -1) this.arpReleaseNote();
        this.arpSetEnabled(on);
        break;
      }
    }
  }
  arpKeyDown(n, v) {                                          // FUN_1800020f0 on every arp note-on
    n = n | 0; if (n < 0 || n > 127) return;
    this.arp.held[n] = 1; this.arp.velocity = v;
    var a = this.arp;
    a.pos = 0; a.octIdx = 0; a.lastIdx = -1;
    a.dir = (a.mode === 3) ? 1 : 0; a.gateOn = true;
  }
  arpKeyUp(n) { n = n | 0; if (n < 0 || n > 127) return; this.arp.held[n] = 0; }
  arpHeld(n) { return this.arp.held[n | 0] !== 0; }
  arpAdvance(n) {                                            // FUN_1800019b0
    var a = this.arp; a.pos += n;
    if (a.stepLen <= a.pos) { var s = (a.pos / a.stepLen) | 0; a.pos = a.pos % a.stepLen; return s; }
    return 0;
  }
  arpSamplesToGateOffEdge() {                                // FUN_1800018f0
    var a = this.arp; if (a.pos === 0) return 0;
    var on = (a.stepLen * a.gate) | 0;
    if (a.pos < on) return on - a.pos;
    if (a.pos !== on) return a.stepLen - a.pos;
    return 0;
  }
  arpNextUp() { var a = this.arp, s = a.lastIdx < 0 ? 0 : a.lastIdx + 1; for (var k = s; k < 128; k++) if (a.held[k]) return k; return -1; }
  arpFirstUp() { for (var k = 0; k < 128; k++) if (this.arp.held[k]) return k; return -1; }
  arpNextDown() { var a = this.arp, s = a.lastIdx < 0 ? 127 : a.lastIdx - 1; for (var k = s; k >= 0; k--) if (a.held[k]) return k; return -1; }
  arpLastDown() { for (var k = 127; k >= 0; k--) if (this.arp.held[k]) return k; return -1; }
  arpRandU() { return crtRand(); }                         /* the shared CRT rand() stream */
  arpRandomHeld() {                                          // FUN_180001930
    var a = this.arp, n = 0;
    for (var k = 0; k < 128; k++) if (a.held[k]) this._arpKeys[n++] = k;
    if (n === 0) return -1;
    return this._arpKeys[crtRand() % n];
  }
  arpEmitStep() {                                            // FUN_180001b40
    var a = this.arp, note = -1;
    if (a.curNote !== -1) a.curNote = -1;                    // owner->noteOff
    if (a.pos !== 0) { a.gateOn = true; return a.stepLen - a.pos; }
    if (a.gate === 0.0) return a.stepLen;
    if (a.mode === 4) {
      a.octIdx = this.arpRandU() % (a.octaves + 1);
      note = this.arpRandomHeld();
    } else if (a.dir === 0) {
      note = this.arpNextUp();
      if (note === -1) {
        var i = a.octIdx;
        if (i < a.octaves) { a.lastIdx = -1; note = this.arpNextUp(); a.octIdx = i + 1; }
        else if (a.mode === 1) {
          a.dir = 1; note = this.arpNextDown();
          if (note === -1 && a.lastIdx >= 0 && a.held[a.lastIdx] && a.octaves > 0) { note = a.lastIdx; a.octIdx = i - 1; }
        } else { a.lastIdx = -1; note = this.arpFirstUp(); a.octIdx = 0; }
      }
    } else {
      note = this.arpNextDown();
      if (note === -1) {
        var j = a.octIdx;
        if (j > 0) { a.lastIdx = -1; note = this.arpLastDown(); a.octIdx = j - 1; }
        else if (a.mode !== 1) { a.lastIdx = -1; note = this.arpLastDown(); a.octIdx = a.octaves; }
        else {
          a.dir = 0;
          note = (a.lastIdx === -1) ? this.arpFirstUp() : this.arpNextUp();
          if (note === -1 && a.lastIdx >= 0 && a.held[a.lastIdx] && a.octaves > 0) { note = a.lastIdx; a.octIdx = j + 1; }
        }
      }
    }
    a.lastIdx = note;
    if (note !== -1) { var midi = note + a.octIdx * 12; if ((midi >>> 0) < 128) a.curNote = midi; }
    if (a.gate < 1.0) a.gateOn = false;
    return (a.stepLen * a.gate) | 0;
  }
  /* engine-level note routing (apply_event / arp_step_boundary) */
  handleNoteOn(note, vel) {
    note = note | 0;
    /* FUN_180028020: the keyboard update runs for every live note-on (arp on
     * or off); the LFO key-sync fires only when this press makes the held-key
     * count 1. Arp-emitted notes never come through here (arpStepBoundary
     * calls noteOn directly), so they never key-sync. */
    if (note >= 0 && note <= 127 && !this.liveKeys[note]) {
      this.liveKeys[note] = 1;
      if (++this.liveKeyCount === 1) this.lfoKeySyncAll();
    }
    if (this.arp.enabled) { this.arpKeyDown(note, vel); return; }
    this.noteOn(note, vel);
  }
  handleNoteOff(note) {
    note = note | 0;
    if (note >= 0 && note <= 127 && this.liveKeys[note]) { this.liveKeys[note] = 0; --this.liveKeyCount; }
    if (this.arp.enabled) { this.arpKeyUp(note); return; }
    this.noteOff(note);
  }
  lfoKeySyncAll() {
    if (this.lfoState[0].keySync) lfoKeySync(this.lfoState[0]);
    if (this.lfoState[1].keySync) lfoKeySync(this.lfoState[1]);
  }
  arpStepBoundary() {
    if (this.arpNote !== -1) this.arpReleaseNote();
    this.arpEmitStep();
    var n = this.arp.curNote;
    if (n >= 0) { this.noteOn(n, this.arp.velocity); this.arpNote = n; }
  }
  arpReleaseNote() {
    if (this.arpNote < 0) return;
    var note = this.arpNote;
    this.voices.forEach(v => { if (v.note === note && v.env < 3) this.startRelease(v); });
    this.arpNote = -1;
  }
  /* state accessors (CVco arp field map §7.1) for tests / panel readback */
  arpCurNote() { return this.arp.curNote; }
  arpGateOn() { return this.arp.gateOn; }
  arpStepLen() { return this.arp.stepLen; }
  arpPosition() { return this.arp.pos; }
  arpGate() { return this.arp.gate; }
  arpOctaveIndex() { return this.arp.octIdx; }
  arpDirection() { return this.arp.dir; }
  arpMode() { return this.arp.mode; }
  arpOctaves() { return this.arp.octaves; }
  arpEnabled() { return this.arp.enabled; }
  arpVelocity() { return this.arp.velocity; }
  arpBeatDiv() { return this.arp.beatDiv; }
  arpTempo() { return this.arp.tempo; }
  arpSeed(s) { crtSrand(s); }   /* the arp shares the ONE CRT rand() stream */

  /* ---------------- Post-voice stereo FX chain (reports/fx_chain_report.md) ----
   * CChorus + CDelay ported from core/fx/chorus.cpp + core/fx/delay.cpp. All
   * ring/line storage is fixed (allocated in the ctor); the per-sample kernels
   * allocate nothing. */
  chorusSetSampleRate(sr) { this._sr = sr; this.chorusSetBaseDelaySeconds(this.chorus.baseDelaySec); this.chorusSetRate(this.chorus.rateHz); }
  chorusSetBaseDelaySeconds(s) {                       // FUN_180003f00
    var c = this.chorus; c.baseDelaySec = s; c.baseDelaySamples = (this._sr * s) | 0;
    this.chorusSetDepth(c.depthParam);
    c.writePos = (c.readPos + c.baseDelaySamples) & CHORUS_LINE_MASK;
    this.chorusRecomputeTailBudget();
  }
  chorusSetDepth(d) {                                  // FUN_180003f90
    var c = this.chorus; c.depthParam = d; c.depthSamples = (c.baseDelaySamples * d) | 0;
    var ds = c.depthSamples < 1 ? 1 : c.depthSamples;
    var step = ((c.lfoPeriod / ds) / 100) | 0; c.depthStep = step < 6 ? 6 : step;
    var span = c.depthSamples * 2 * Math.PI;
    c.depthNorm = span <= c.lfoPeriod ? 1 : c.lfoPeriod / span;
  }
  chorusSetRate(hz) {                                  // FUN_180004110
    var c = this.chorus; c.rateHz = hz; c.lfoPeriod = (this._sr / hz) | 0;
    var ds = c.depthSamples < 1 ? 1 : c.depthSamples;
    var step = ((c.lfoPeriod / ds) / 100) | 0; c.depthStep = step < 6 ? 6 : step;
    c.phaseStep = 2 * Math.sin(hz * Math.PI / this._sr);
    var span = c.depthSamples * 2 * Math.PI;
    c.depthNorm = span <= c.lfoPeriod ? 1 : c.lfoPeriod / span;
  }
  chorusSetFeedback(fb) {
    var c = this.chorus; c.feedback = fb; c.feedbackOn = fb === 0 ? 0 : 1;
    this.chorusRecomputeTailBudget();   // FUN_1800040b0 → FUN_180003610
  }
  chorusRecomputeTailBudget() {        // FUN_180003610
    var c = this.chorus;
    var old = c.tailBudget;
    var ratio = Math.log(3.0517578125e-05) / Math.log(Math.abs(c.feedback));
    if (!(ratio > 0)) ratio = 0;
    c.tailBudget = ((ratio | 0) + 2) * c.baseDelaySamples;
    /* A (staged law): never push the ctor sentinel past the budget. */
    if (c.silentFrames === 99999999) { /* sentinel: ring out from first gap */ }
    else if (c.silentFrames > old) c.silentFrames = c.tailBudget + 1;
    else c.silentFrames = 0;
  }
  chorusSetLevel(l) { this.chorus.level = l; }
  chorusSetMode(m) {  // FUN_1800040e0: keep 1/2/4, map 3 (and out-of-range) to 2
    var c = this.chorus;
    c.mode = (((m - 1) & ~3) === 0 && m !== 3) ? m : 2;
  }
  chorusSetOn(on) {                                    // FUN_180004060 rising edge clears the line
    var c = this.chorus; if (on && !c.onOff) { c.lineL.fill(0); c.lineR.fill(0); } c.onOff = on ? 1 : 0;
  }

  delaySetSampleRate(sr) {                             // FUN_180005780 / setSampleRate
    this._sr = sr; var d = this.delay;
    d.timeSamp = (sr * d.timeSec) | 0;
    d.tapSlew = 1 - Math.pow(0.5, 1 / (sr * 0.15));
    this.delayRecomputeTaps();
    if (d.toneFreq > 0) this.delaySetToneFilter(d.toneType, d.toneFreq);
  }
  delaySetTimeSeconds(s) { var d = this.delay; d.timeSec = s; d.timeSamp = (this._sr * s) | 0; this.delayRecomputeTaps(); }
  delaySetTempoSyncBeatIndex(idx) { this.delaySetTimeSeconds(delaySyncSeconds(idx, this.arp.tempo)); }
  delaySetFeedback(fb) {
    var d = this.delay; d.feedback = fb < 0 ? 0 : (fb > DELAY_FB_MAX ? DELAY_FB_MAX : fb);
    this.delayRecomputeTailBudget();   // FUN_180006b10 → FUN_180005ab0
  }
  delaySetDryWet(x) { var d = this.delay; d.wet = delayWetLevel(x); d.dry = delayDryLevel(x); }
  delaySetSpread(s) { var d = this.delay; d.spread = s; this.delayRecomputeTaps(); }
  delaySetMode(m) { this.delay.mode = m; this.delayRecomputeTailBudget(); }  // FUN_180006ba0
  delayRecomputeTailBudget() {         // FUN_180005ab0
    var d = this.delay;
    var old = d.tailBudget;
    /* A (staged law): the ctor sentinel 99999999 means "never counted" —
     * device rings the FIRST gap, so the sentinel must never be pushed. */
    var ratio = Math.log(3.0517578125e-05) / Math.log(d.feedback);
    if (!(ratio > 0)) ratio = 0;
    var period = d.leftTap > d.rightTap ? d.leftTap : d.rightTap;
    if (d.mode === 2) period += period;   // ping-pong: the round trip
    d.tailBudget = ((ratio | 0) + 2) * period;
    if (d.silentFrames !== 99999999 && d.silentFrames > old) d.silentFrames = d.tailBudget + 1;
  }
  delaySetOn(on) {                                     // FUN_180006a80 rising edge clears lines
    var d = this.delay;
    if (on && !d.onOff) {
      d.writePos = 0; d.slewing = 0; d.rightLive = d.rightTap; d.leftLive = d.leftTap;
      d.lineL.fill(0); d.lineR.fill(0);
    }
    d.onOff = on ? 1 : 0;
  }
  delaySetToneParam(x) {                               // FUN_180028b10 (param 98)
    if (x === 64) { this.delaySetToneFilter(0, 0); return; }
    if (x < 64) this.delaySetToneFilter(1, Math.pow(110, x / 63) * 200);
    else this.delaySetToneFilter(2, Math.pow(800, (x - 65) / 62) * 10);
  }
  delaySetToneFilter(type, freq) {                     // CEq one-pole shelf (spec §4.1/§4.2)
    var d = this.delay; d.toneType = type; d.toneFreq = freq;
    if (type === 0) return;
    var f = freq > 1 ? freq : 1, w = f * 2 * Math.PI, twoSr = this._sr * 2, k = 1 / (w + twoSr);
    d.toneA0 = w * k; d.toneA2 = (twoSr - w) * k;
    if (type === 2) d.toneA0 = twoSr * k;
  }
  delayRecomputeTaps() {                               // FUN_1800059c0
    var d = this.delay, t = (d.timeSamp + 2) & ~3, right = t, left = t;
    if (d.spread < 0) right = ((-d.spread * this._sr) | 0) + t;
    else left = ((d.spread * this._sr) | 0) + t;
    var lo = (this._sr * 0.0001) | 0, hi = DELAY_LINE_SIZE - 256;
    right = clamp(right, lo, hi); left = clamp(left, lo, hi);
    d.rightTap = right; d.leftTap = left; d.rightLive = right; d.leftLive = left;
    this.delayRecomputeTailBudget();   // FUN_1800059c0 → FUN_180005ab0
  }

  fxParam(id, v) {                                     // engine dispatch_param → FxChain::set_param
    switch (id) {
      case 52: this.chorusSetBaseDelaySeconds(chorusBaseDelayMs(v) * 0.001); break;
      case 53: this.chorusSetDepth(chorusDepth(v)); break;
      case 54: this.chorusSetRate(chorusRateHz(v)); break;
      case 55: this.chorusSetFeedback(chorusFb(v)); break;
      case 56: this.chorusSetLevel(chorusLevel(v)); break;
      case 64: this.chorusSetMode(v); break;
      case 66: this.chorusSetOn(v !== 0); break;
      case 35: this.delayBeatIndex = clamp(v | 0, 0, 19); this.delaySetTempoSyncBeatIndex(this.delayBeatIndex); break;
      case 36: this.delaySetFeedback(v / 127); break;
      case 37: this.delaySetDryWet(v); break;
      case 65: this.delaySetOn(v !== 0); break;
      case 82: this.delaySetMode(v); break;
      case 83: this.delaySetSpread(delaySpreadSec(v)); break;
      case 98: this.delaySetToneParam(v); break;
      case 90: this._pan90 = cpanLaw(v); break;
      case 73: this.unisonOn = (v === 1); this.recomputeVoicePans(); this.recomputeVoiceDetune(); break;
      case 75: this.recomputeVoiceDetune(); break;
      case 84: this.recomputeVoicePans(); break;
      case 85: this.recomputeVoiceDetune(); break;
      case 93: { var n = 2 + Math.round(v * 6 / 127); this.unisonCount = clamp(n, 2, 8); this.recomputeVoicePans(); this.recomputeVoiceDetune(); break; }
      case 60: case 61: case 62: case 63: this.eqParam(id, v); break;
      case 77: case 78: case 79: case 80: case 81: this.effectorSetParam(id, v); break;
      default: break;
    }
  }

  recomputeVoicePans() {                               // FUN_180037250
    var N = this.unisonCount;
    if (!this.unisonOn || N < 2) { this.voicePan.fill(0); return; }
    var spread = (clamp(this.P(84, 64), 0, 127) - 64) / 64;
    for (var i = 0; i < 32; i++) this.voicePan[i] = panSpreadLaw(spread, i, N);
  }

  recomputeVoiceDetune() {                             // FUN_180037130 pool pass
    var N = this.unisonCount;
    var on = this.unisonOn && N >= 2;
    for (var i = 0; i < this.voices.length; i++) {
      var v = this.voices[i];
      v.detuneCents = on ? unisonSlotPitchCents(v.slot % N, N, this.P(75, 22), this.P(85, 24)) : 0;
    }
  }

  /* ---- CEffector (fx/effector.cpp) --------------------------------------- */
  efF0(v) { return 1 - 1 / (1 + 2 * v * v * (v + 0.4)); }
  efF1(t) { return 1 - 1 / (1 + t * t * (t + 1)); }
  efDrive(ctl1raw) {                                   // 10^((20u-10)*0.05)
    return Math.pow(10, (20 * (ctl1raw / 127) - 10) * 0.05);
  }
  efToneCoef(raw) {                                    // ctl2 -> one-pole LP
    if (raw >= 127) return 1;
    var fc = 20 * Math.pow(1000, raw / 127);
    return 1 - Math.exp(-2 * Math.PI * fc / this._sr);
  }
  efCompCoef(ctl2raw) {                                // t = 2000^sqrt(u)*0.1 ms
    this.efComp.ctl2raw = ctl2raw;
    var t = Math.pow(2000, Math.sqrt(ctl2raw / 127)) * 0.1;
    var sec = (t > 0 ? t : 0.1) * 0.001;
    var coef = 1 - Math.exp(-1 / (this._sr * sec));
    this.efComp.atk = coef; this.efComp.rel = coef;
  }
  efPhaserStep() {
    var p = this.efPh;
    if (p.rate <= 0) p.rate = 0.01;
    var nsamp = this._sr / p.rate;
    if (nsamp < 1) nsamp = 1;
    p.gStep = Math.pow(0.98 / 0.02, 1 / nsamp);
  }
  efNorm() {
    var d = this.efDist;
    d.norm = d.curve === 0 ? (this.efF0(d.drive) > 0 ? 2 / this.efF0(d.drive) : 2)
                           : (this.efF1(d.drive) > 0 ? 1 / this.efF1(d.drive) : 1);
  }
  effectorSetSampleRate(sr) {
    this.efDist.toneA = this.efToneCoef(this.efDist.toneCut);
    this.efCompCoef(this.efComp.ctl2raw);
    this.efRm.k = 2 * Math.sin(Math.PI * this.efRm.freq / sr);
    this.efPhaserStep();
  }
  effectorReset() {                                    // rising-edge on/off
    this.efDist.y1L = this.efDist.y1R = 0;
    this.efComp.envL = this.efComp.envR = 0;
    this.efRm.s0 = 1; this.efRm.s1 = 0;
    this.efDec.cnt = 0; this.efDec.heldL = this.efDec.heldR = 0;
    var p = this.efPh;
    p.s.fill(0); p.accL = 0; p.accR = 0; p.g = 0.02; p.frozen = false;
    this.efPhaserStep();
  }
  effectorSetParam(id, v) {                            // CEffector::set_param
    switch (id) {
      case 77: { var prev = this.efOn; this.efOn = v; if (v !== 0 && prev === 0) this.effectorReset(); break; }
      case 78: {
        this.efType = clamp(v | 0, 0, 9);
        if (this.efType <= 2) { this.efDist.curve = clamp(this.efType, 0, 2); this.efNorm(); }
        else if (this.efType >= 6) this.efPh.nPairs = clamp([1, 2, 4, 6][this.efType - 6], 1, 6);
        break;
      }
      case 79: {                                      // ctl1 broadcast
        this.efCtl1 = v;
        this.efDist.drive = this.efDrive(v); this.efNorm();
        this.efComp.thrDb = -20 - 40 * (v / 127);
        this.efComp.thrLin = Math.pow(10, this.efComp.thrDb / 20);
        this.efRm.freq = Math.pow(8000, v / 127);
        this.efRm.k = 2 * Math.sin(Math.PI * this.efRm.freq / this._sr);
        this.efDec.period = v + 1;
        break;
      }
      case 80: {                                      // ctl2 broadcast
        this.efCtl2 = v;
        this.efDist.toneCut = v; this.efDist.toneA = this.efToneCoef(v);
        this.efCompCoef(v);
        this.efDec.mask = (-1) << (((v >> 3) + 1) & 0x1f);
        this.efPh.rate = (v === 0) ? 0.01 : Math.pow(1000, v / 127) * 0.02;
        this.efPhaserStep();
        break;
      }
      case 81: {                                      // level broadcast
        this.efLevel = v;
        this.efDist.level = (v + 2) / 129;
        this.efComp.makeup = 2 * v / 127;
        this.efRm.level = v / 127;
        this.efDec.mix = v / 127;
        var fb = (v - 64) / 64 * 0.99;
        this.efPh.fb = clamp(fb, -0.99, 0.99);
        break;
      }
      default: break;
    }
  }
  effectorProcess(L, R, N) {                           // CEffector::process
    if (this.efOn === 0) return;                       // bypass: untouched
    var i, d, c, rm, dc, ph;
    switch (this.efType) {
      case 0: case 1: case 2:
        d = this.efDist;
        if (d.curve === 0) {
          for (i = 0; i < N; i++) {
            var xl0 = L[i] * d.drive, xr0 = R[i] * d.drive;
            var ol = (xl0 >= 0 ? this.efF0(xl0) : 0) * d.norm * d.level;
            var or_ = (xr0 >= 0 ? this.efF0(xr0) : 0) * d.norm * d.level;
            if (d.toneA < 1) { ol = d.y1L + d.toneA * (ol - d.y1L); d.y1L = ol;
                               or_ = d.y1R + d.toneA * (or_ - d.y1R); d.y1R = or_; }
            L[i] = ol; R[i] = or_;
          }
        } else {
          for (i = 0; i < N; i++) {
            var xl = L[i], xr = R[i];
            var sl = this.efF1((Math.abs(xl) + 1e-4) * d.drive);
            var sr = this.efF1((Math.abs(xr) + 1e-4) * d.drive);
            var ol2 = (xl < 0 ? -1 : 1) * sl * d.norm * d.level;
            var or2 = (xr < 0 ? -1 : 1) * sr * d.norm * d.level;
            if (d.toneA < 1) { ol2 = d.y1L + d.toneA * (ol2 - d.y1L); d.y1L = ol2;
                               or2 = d.y1R + d.toneA * (or2 - d.y1R); d.y1R = or2; }
            L[i] = ol2; R[i] = or2;
          }
        }
        break;
      case 3:
        dc = this.efDec;
        for (i = 0; i < N; i++) {
          if ((dc.cnt % dc.period) === 0) {
            dc.heldL = ((((L[i] * 65536) | 0) & dc.mask)) / 65536;
            dc.heldR = ((((R[i] * 65536) | 0) & dc.mask)) / 65536;
          }
          L[i] = dc.heldL * dc.mix + (1 - dc.mix) * L[i];
          R[i] = dc.heldR * dc.mix + (1 - dc.mix) * R[i];
          dc.cnt++;
        }
        break;
      case 4:
        rm = this.efRm;
        for (i = 0; i < N; i++) {
          var cc = rm.s0 - rm.k * rm.s1;
          rm.s0 = cc; rm.s1 = cc * rm.k + rm.s1;
          var g = rm.s0 * rm.level + (1 - rm.level);
          L[i] *= g; R[i] *= g;
        }
        break;
      case 5:
        c = this.efComp;
        for (i = 0; i < N; i++) {
          var axl = Math.abs(L[i]);
          c.envL += (axl - c.envL) * (axl > c.envL ? c.atk : c.rel);
          L[i] = L[i] * (c.envL > c.thrLin ? Math.pow(c.thrLin / c.envL, 4) : 1) * c.makeup;
          var axr = Math.abs(R[i]);
          c.envR += (axr - c.envR) * (axr > c.envR ? c.atk : c.rel);
          R[i] = R[i] * (c.envR > c.thrLin ? Math.pow(c.thrLin / c.envR, 4) : 1) * c.makeup;
        }
        break;
      case 6: case 7: case 8: case 9: {
        ph = this.efPh;
        if (ph.nPairs <= 0) return;
        var st, b, a, bb, h0, h1, h2, h3;
        for (i = 0; i < N; i++) {
          if (!ph.frozen) { ph.g *= ph.gStep; if (ph.g > 0.98) ph.g = 0.02; }
          var v = (1 - ph.g) / (ph.g + 1);
          ph.accR = ph.fb * ph.accR + R[i];
          ph.accL = ph.fb * ph.accL + L[i];
          var xpl = ph.accL, xpr = ph.accR;
          for (st = 0; st < ph.nPairs; st++) {
            b = st * 4;
            h0 = ph.s[b]; h1 = ph.s[b + 1]; h2 = ph.s[b + 2]; h3 = ph.s[b + 3];
            a = h0 - xpr * v; bb = a * v; h0 = bb + xpr; xpr = h1 - bb; h1 = xpr * v + a;
            a = h2 - xpl * v; bb = a * v; h2 = bb + xpl; xpl = h3 - bb; h3 = xpl * v + a;
            ph.s[b] = h0; ph.s[b + 1] = h1; ph.s[b + 2] = h2; ph.s[b + 3] = h3;
          }
          L[i] = xpl; R[i] = xpr;
        }
        break;
      }
      default: break;
    }
  }

  /* ---- CEq (fx/eq.cpp) ---------------------------------------------------- */
  mkEq(type) {
    return { enabled: 1, dirty: 1, type: type, f: 1000, g: 0, q: 1,
             a0: 1, a1: 0, a2: 0, b1: 0, b2: 0,
             l: { x1: 0, x2: 0, y1: 0, y2: 0 }, r: { x1: 0, x2: 0, y1: 0, y2: 0 } };
  }
  eqParam(id, v) {                                     // FxChain::set_param 60..63
    var eqA = this.eqA, eqB = this.eqB;
    if (id === 60) {
      if (v < 65) { eqB.type = 1; eqB.f = 200 * Math.pow(110, v / 64); }
      else { eqB.type = 2; eqB.f = 10 * Math.pow(800, (v - 64) / 64); }
      eqB.dirty = 1;
    } else if (id === 61) { eqA.f = 50 * Math.pow(320, v / 127); eqA.dirty = 1; }
    else if (id === 62) { eqA.g = (v - 64) / 127 * 50; eqA.dirty = 1; }
    else if (id === 63) { eqA.q = Math.pow(10, v / 127); eqB.q = eqA.q;
                          eqA.dirty = 1; eqB.dirty = 1; }
  }
  eqPrepare(eq) {
    eq.dirty = 0;
    var f = clamp(eq.f, 10, 0.499 * this._sr);
    var q = clamp(eq.q, 0.05, 1000);
    var w = 2 * Math.PI * f / this._sr;
    var cw = Math.cos(w), sw = Math.sin(w);
    if (eq.type === 0) {                               // RBJ peaking (matched form)
      var al = Math.pow(10, eq.g * 0.025);
      var alpha = sw / (2 * q);
      var na = 1 + alpha / al;
      eq.a0 = (1 + alpha * al) / na;
      eq.a1 = -2 * cw / na;
      eq.a2 = (1 - alpha * al) / na;
      eq.b1 = -2 * cw / na;
      eq.b2 = (1 - alpha / al) / na;
    } else {                                           // FUN_18000d4a0 shelf kernels
      var wz = 2 * Math.PI * f;
      var twoSr = this._sr * 2;
      var k = 1 / (wz + twoSr);
      var pole = (twoSr - wz) * k;
      if (eq.type === 1) { eq.a0 = k * wz; eq.a1 = k * wz; }
      else { eq.a0 = k * twoSr; eq.a1 = -k * twoSr; }
      eq.a2 = 0; eq.b1 = -pole; eq.b2 = 0;
    }
  }
  eqProcess(eq, L, R, N) {
    if (!eq.enabled || N <= 0) return;
    if (eq.dirty) this.eqPrepare(eq);
    var l = eq.l, r = eq.r;
    for (var i = 0; i < N; i++) {
      var xl = L[i];
      var yl = eq.a0 * xl + eq.a1 * l.x1 + eq.a2 * l.x2 - eq.b1 * l.y1 - eq.b2 * l.y2;
      l.x2 = l.x1; l.x1 = xl; l.y2 = l.y1; l.y1 = yl;
      L[i] = yl;
      var xr = R[i];
      var yr = eq.a0 * xr + eq.a1 * r.x1 + eq.a2 * r.x2 - eq.b1 * r.y1 - eq.b2 * r.y2;
      r.x2 = r.x1; r.x1 = xr; r.y2 = r.y1; r.y1 = yr;
      R[i] = yr;
    }
  }

  /* CDelay::process (FUN_180006810) IN PLACE over [0,numFrames); chainMode tail
   * leaves wet·input in the chain buffer and dry·tone taps in the tone scratch. */
  delayProcess(left, right, numFrames, ioSilent) {
    var d = this.delay;
    if (!d.onOff) { d.outActive = 0; return; }
    /* FUN_180006810 silent-input gate: ring out for tailBudget frames past the
     * last non-silent input, then report outActive = 0. */
    if (ioSilent) {
      if (ioSilent.v === 0) {
        d.silentFrames = 0;
      } else if (d.silentFrames === 99999999) {
        /* A (staged law): first silent block after boot starts counting —
         * device rings the first gap. */
        d.silentFrames = numFrames;
      } else {
        if (d.tailBudget < d.silentFrames) {
          if (d.slewing === 0) { d.outActive = 0; return; }
        } else {
          d.silentFrames += numFrames;
        }
        ioSilent.v = 0;
        for (var i = 0; i < numFrames; i++) { left[i] = 0; right[i] = 0; }
      }
    }
    var total = 0;
    while (total < numFrames) {
      var remaining = numFrames - total;
      if (remaining > DELAY_MAX_FRAMES) remaining = DELAY_MAX_FRAMES;
      var count = remaining;
      if (d.slewing === 0) { var m = Math.min(d.leftTap, d.rightTap); if (count > m) count = m; }
      else count = 1;
      if (count <= 0) count = 1;
      if (d.mode === 2) this.delayProcessPingPong(left, right, total, count);
      else this.delayProcessNormal(left, right, total, count);
      total += count;
      if (d.slewing !== 0) {
        if (Math.abs(d.rightLive - d.rightTap) < DELAY_TAP_EPS) d.rightLive = d.rightTap;
        if (Math.abs(d.leftLive - d.leftTap) < DELAY_TAP_EPS) d.leftLive = d.leftTap;
        if (d.rightLive === d.rightTap && d.leftLive === d.leftTap) d.slewing = 0;
      }
    }
    if (d.chainMode) {
      for (var i = 0; i < numFrames; i++) {
        left[i] *= d.wet; right[i] *= d.wet; d.toneL[i] *= d.dry; d.toneR[i] *= d.dry;
      }
    } else {
      for (var i = 0; i < numFrames; i++) {
        left[i] = d.wet * left[i] + d.dry * d.toneL[i];
        right[i] = d.wet * right[i] + d.dry * d.toneR[i];
      }
    }
    d.outActive = 1;   // FUN_180006810 tail: the output is live again
  }
  delayProcessNormal(left, right, off, count) {        // FUN_180006090
    var d = this.delay, w = d.writePos;
    if (d.slewing === 0) {
      for (var i = 0; i < count; i++) {
        d.toneL[off + i] = d.lineL[(w - d.rightTap + i) & DELAY_LINE_MASK];
        d.toneR[off + i] = d.lineR[(w - d.leftTap + i) & DELAY_LINE_MASK];
      }
    } else {
      var pr = d.rightLive, pl = d.leftLive, k = d.tapSlew;
      for (var i = 0; i < count; i++) {
        pr += (d.rightTap - pr) * k; pl += (d.leftTap - pl) * k;
        var fr = (i + w) - pr; if (fr < 0) fr += DELAY_LINE_SIZE;
        var fl = (i + w) - pl; if (fl < 0) fl += DELAY_LINE_SIZE;
        var ir = fr | 0, il = fl | 0;
        var aL = d.lineL[il & DELAY_LINE_MASK], bL = d.lineL[(il + 1) & DELAY_LINE_MASK];
        var aR = d.lineR[ir & DELAY_LINE_MASK], bR = d.lineR[(ir + 1) & DELAY_LINE_MASK];
        d.toneL[off + i] = aL + (bL - aL) * (fl - il);
        d.toneR[off + i] = aR + (bR - aR) * (fr - ir);
      }
      d.rightLive = pr; d.leftLive = pl;
    }
    this.delayToneFilter(off, count);
    var fb = d.feedback;
    if (d.mode === 1) {
      for (var i = 0; i < count; i++) {
        var p = (w + i) & DELAY_LINE_MASK;
        d.lineL[p] = fb * d.toneR[off + i] + right[off + i];
        d.lineR[p] = fb * d.toneL[off + i] + left[off + i];
      }
    } else {
      for (var i = 0; i < count; i++) {
        var p = (w + i) & DELAY_LINE_MASK;
        d.lineL[p] = fb * d.toneL[off + i] + left[off + i];
        d.lineR[p] = fb * d.toneR[off + i] + right[off + i];
      }
    }
    d.writePos = (w + count) & DELAY_LINE_MASK;
  }
  delayProcessPingPong(left, right, off, count) {      // FUN_180005b20
    var d = this.delay, w = d.writePos;
    if (d.slewing === 0) {
      for (var i = 0; i < count; i++) {
        d.toneL[off + i] = d.lineL[(w - d.rightTap + i) & DELAY_LINE_MASK];
        d.toneR[off + i] = d.lineR[(w - d.leftTap + i) & DELAY_LINE_MASK];
      }
    } else {
      var pr = d.rightLive, pl = d.leftLive, k = d.tapSlew;
      for (var i = 0; i < count; i++) {
        pr += (d.rightTap - pr) * k; pl += (d.leftTap - pl) * k;
        var fr = (i + w) - pr; if (fr < 0) fr += DELAY_LINE_SIZE;
        var fl = (i + w) - pl; if (fl < 0) fl += DELAY_LINE_SIZE;
        var ir = fr | 0, il = fl | 0;
        var aL = d.lineL[ir & DELAY_LINE_MASK], bL = d.lineL[(ir + 1) & DELAY_LINE_MASK];
        var aR = d.lineR[il & DELAY_LINE_MASK], bR = d.lineR[(il + 1) & DELAY_LINE_MASK];
        d.toneL[off + i] = aL + (bL - aL) * (fr - ir);
        d.toneR[off + i] = aR + (bR - aR) * (fl - il);
      }
      d.rightLive = pr; d.leftLive = pl;
    }
    this.delayToneFilter(off, count);
    var fb = d.feedback;
    for (var i = 0; i < count; i++) {
      var p = (w + i) & DELAY_LINE_MASK;
      d.lineL[p] = (left[off + i] + right[off + i]) * 0.5 + fb * d.toneL[off + i];
      d.lineR[p] = d.toneR[off + i];
    }
    d.writePos = (w + count) & DELAY_LINE_MASK;
  }
  delayToneFilter(off, count) {                        // integrated one-pole shelf over the tone scratch
    var d = this.delay;
    if (d.toneType === 0) return;
    var a0 = d.toneA0, a2 = d.toneA2, x1l = d.toneX1L, x1r = d.toneX1R, y1l = d.toneY1L, y1r = d.toneY1R;
    if (d.toneType === 1) {
      for (var i = off; i < off + count; i++) {
        var xl = d.toneL[i], xr = d.toneR[i];
        y1l = a0 * (xl + x1l) + a2 * y1l; y1r = a0 * (xr + x1r) + a2 * y1r;
        x1l = xl; x1r = xr; d.toneL[i] = y1l; d.toneR[i] = y1r;
      }
    } else {
      for (var i = off; i < off + count; i++) {
        var xl = d.toneL[i], xr = d.toneR[i];
        y1l = a0 * (xl - x1l) + a2 * y1l; y1r = a0 * (xr - x1r) + a2 * y1r;
        x1l = xl; x1r = xr; d.toneL[i] = y1l; d.toneR[i] = y1r;
      }
    }
    d.toneX1L = x1l; d.toneX1R = x1r; d.toneY1L = y1l; d.toneY1R = y1r;
  }

  /* CChorus::process (FUN_1800036d0) IN PLACE in CHORUS_SUB_BLOCK sub-blocks.
   * Off path: the delay tone buffer is ADDED directly to the output (no
   * double-count with the chain buffer). On path: ring = (chain + tone)·level. */
  chorusProcess(left, right, numFrames, ioSilent) {
    var c = this.chorus;
    if (!c.onOff) {
      if (c.toneL && c.toneR) {
        for (var i = 0; i < numFrames; i++) { left[i] += c.toneL[i]; right[i] += c.toneR[i]; }
      }
      return;
    }
    /* FUN_1800036d0 silent-input gate: the delay upstream clears the flag
     * while it is ringing; the chorus starts counting only once the delay has
     * given up, rings its own line for tailBudget frames, then stops. */
    if (ioSilent) {
      if (ioSilent.v === 0 || c.delayActive) {
        c.silentFrames = 0;
      } else if (c.silentFrames === 99999999) {
        /* A (staged law): chorus rings its own first gap. */
        c.silentFrames = numFrames;
      } else {
        if (c.tailBudget < c.silentFrames) return numFrames;
        c.silentFrames += numFrames;
        for (var i = 0; i < numFrames; i++) { left[i] = 0; right[i] = 0; }
      }
    }
    var done = 0;
    while (done < numFrames) {
      var n = numFrames - done;
      if (n > CHORUS_SUB_BLOCK) n = CHORUS_SUB_BLOCK;
      this.chorusSubBlock(left, right, done, n);
      done += n;
    }
  }
  chorusSubBlock(left, right, off, numFrames) {
    var c = this.chorus, toneL = c.toneL, toneR = c.toneR;
    var first = CHORUS_LINE_SIZE - c.writePos;
    if (numFrames < first) first = numFrames;
    for (var i = 0; i < first; i++) {
      var tl = toneL ? toneL[off + i] : 0, tr = toneR ? toneR[off + i] : 0;
      c.lineL[c.writePos + i] = (left[off + i] + tl) * c.level;
      c.lineR[c.writePos + i] = (right[off + i] + tr) * c.level;
    }
    for (var i = first; i < numFrames; i++) {
      var j = i - first;
      var tl = toneL ? toneL[off + i] : 0, tr = toneR ? toneR[off + i] : 0;
      c.lineL[j] = (left[off + i] + tl) * c.level;
      c.lineR[j] = (right[off + i] + tr) * c.level;
    }
    if (c.oscS1 > CHORUS_OSC_CLAMP) { c.oscS0 = 0; c.oscS1 = CHORUS_OSC_CLAMP; }
    var dq = (c.depthSamples * c.depthNorm) | 0;
    var dqn16 = (dq << 16) >>> 0;
    var k = c.phaseStep, fb = c.feedback, rp = c.readPos, wp = c.writePos;
    var INV65536 = 1 / 65536;
    if (c.mode === 1) {
      for (var i = 0; i < numFrames; i++) {
        var cc = c.oscS0 - k * c.oscS1; c.oscS0 = cc; c.oscS1 = cc * k + c.oscS1;
        var u = (dqn16 * cc) + (rp << 16);
        var idx = ((u >>> 0) & 0x1FFFFFFF) >> 16, frac = ((u >>> 0) & 0xFFFF) * INV65536;
        var l = c.lineL[idx] + (c.lineL[(idx + 1) & CHORUS_LINE_MASK] - c.lineL[idx]) * frac;
        var r = c.lineR[idx] + (c.lineR[(idx + 1) & CHORUS_LINE_MASK] - c.lineR[idx]) * frac;
        left[off + i] = left[off + i] * c.dryGain + l;
        right[off + i] = right[off + i] * c.dryGain + r;
        c.lineL[wp] += l * fb; c.lineR[wp] += r * fb;
        rp = (rp + 1) & CHORUS_LINE_MASK; wp = (wp + 1) & CHORUS_LINE_MASK;
      }
    } else if (c.mode === 2) {
      for (var i = 0; i < numFrames; i++) {
        var cc = c.oscS0 - k * c.oscS1; c.oscS0 = cc; c.oscS1 = cc * k + c.oscS1;
        var uL = (dqn16 * c.oscS0) + (rp << 16), uR = (dqn16 * c.oscS1) + (rp << 16);
        var iL = ((uL >>> 0) & 0x1FFFFFFF) >> 16, fL = ((uL >>> 0) & 0xFFFF) * INV65536;
        var iR = ((uR >>> 0) & 0x1FFFFFFF) >> 16, fR = ((uR >>> 0) & 0xFFFF) * INV65536;
        var l = c.lineL[iL] + (c.lineL[(iL + 1) & CHORUS_LINE_MASK] - c.lineL[iL]) * fL;
        var r = c.lineR[iR] + (c.lineR[(iR + 1) & CHORUS_LINE_MASK] - c.lineR[iR]) * fR;
        left[off + i] += l; right[off + i] += r;
        c.lineL[wp] += l * fb; c.lineR[wp] += r * fb;
        rp = (rp + 1) & CHORUS_LINE_MASK; wp = (wp + 1) & CHORUS_LINE_MASK;
      }
    } else {
      for (var i = 0; i < numFrames; i++) {
        var cc = c.oscS0 - k * c.oscS1; c.oscS0 = cc; c.oscS1 = cc * k + c.oscS1;
        var uA = (dqn16 * c.oscS0) + (rp << 16), uB = (dqn16 * c.oscS1) + (rp << 16);
        var tA = ((uA >>> 0) & 0x1FFFFFFF) >> 16, fA = ((uA >>> 0) & 0xFFFF) * INV65536, rA = (0x10000 - ((uA >>> 0) & 0xFFFF)) * INV65536;
        var tB = ((uB >>> 0) & 0x1FFFFFFF) >> 16, fB = ((uB >>> 0) & 0xFFFF) * INV65536, rB = (0x10000 - ((uB >>> 0) & 0xFFFF)) * INV65536;
        var mA = (rp * 2 - tA) & CHORUS_LINE_MASK, mB = (rp * 2 - tB) & CHORUS_LINE_MASK;
        var T0 = c.lineL[(mA - 1) & CHORUS_LINE_MASK] + (c.lineL[mA] - c.lineL[(mA - 1) & CHORUS_LINE_MASK]) * rA;
        var T1 = c.lineL[tA] + (c.lineL[(tA + 1) & CHORUS_LINE_MASK] - c.lineL[tA]) * fA;
        var T2 = c.lineR[tB] + (c.lineR[(tB + 1) & CHORUS_LINE_MASK] - c.lineR[tB]) * fB;
        var T3 = c.lineR[(mB - 1) & CHORUS_LINE_MASK] + (c.lineR[mB] - c.lineR[(mB - 1) & CHORUS_LINE_MASK]) * rB;
        var oL = left[off + i], oR = right[off + i];
        left[off + i] = T3 * 0.3 + T1 * 0.9 + T0 * 0.1 + T2 * 0.7 + oL;
        right[off + i] = T2 * 0.3 + T1 * 0.1 + T0 * 0.9 + T3 * 0.7 + oR;
        c.lineL[wp] += T1 * fb; c.lineR[wp] += T2 * fb;
        rp = (rp + 1) & CHORUS_LINE_MASK; wp = (wp + 1) & CHORUS_LINE_MASK;
      }
    }
    c.readPos = (c.readPos + numFrames) & CHORUS_LINE_MASK;
    c.writePos = (c.writePos + numFrames) & CHORUS_LINE_MASK;
  }

  /* chain driver (§9): CPan(90) → CDelay → CChorus, IN PLACE over the block. */
  fxProcess(L, R, N) {
    /* FxChain::process: effector -> eqA -> eqB -> pan -> delay -> chorus. The
     * "input is silent" flag is derived from the block BEFORE the chain
     * (core computes it pre-effector) and drives both FX ring-out budgets. */
    var io = { v: 1 };
    for (var i = 0; i < N; i++) {
      if (L[i] !== 0 || R[i] !== 0) { io.v = 0; break; }
    }
    this.effectorProcess(L, R, N);
    this.eqProcess(this.eqA, L, R, N);
    this.eqProcess(this.eqB, L, R, N);
    var p = this._pan90;
    if (p.gl !== 1 || p.gr !== 1) {
      for (var i = 0; i < N; i++) { L[i] *= p.gl; R[i] *= p.gr; }
    }
    this.delayProcess(L, R, N, io);
    var toneSend = this.delay.onOff ? 1 : 0;
    this.chorus.toneL = toneSend ? this.delay.toneL : null;
    this.chorus.toneR = toneSend ? this.delay.toneR : null;
    this.chorus.delayActive = this.delay.outActive;
    this.chorusProcess(L, R, N, io);
  }

  /* law helpers exposed for unit tests (analytic values from fx_chain_report.md) */
  chorusBaseDelayMs(x) { return chorusBaseDelayMs(x); }
  chorusRateHz(x) { return chorusRateHz(x); }
  chorusDepth(x) { return chorusDepth(x); }
  chorusFb(x) { return chorusFb(x); }
  chorusLevel(x) { return chorusLevel(x); }
  delaySpreadSec(x) { return delaySpreadSec(x); }
  delaySyncSeconds(i, t) { return delaySyncSeconds(i, t); }
  delayWetLevel(x) { return delayWetLevel(x); }
  delayDryLevel(x) { return delayDryLevel(x); }
  panSpreadLaw(s, i, n) { return panSpreadLaw(s, i, n); }
  mixerPanLaw(p) { return mixerPanLaw(p); }
  cpanLaw(x) { return cpanLaw(x); }

  oscSample(type, ph) {
    switch (type) {
      case 'sine': return Math.sin(2 * Math.PI * ph);
      case 'sawtooth': return 2 * ph - 1;
      case 'square': return ph < 0.5 ? 1 : -1;
      default: return ph < 0.25 ? 4 * ph : (ph < 0.75 ? 2 - 4 * ph : 4 * ph - 4);
    }
  }

  /* ---------------- CVcf filter stage (core/filter/filter.cpp) -------------
   * Per-voice ladder filter state, allocation-free (flat fields on the voice).
   * Chain per sample: cutoff slew -> coefficient cache -> core -> leveler ->
   * soft-clip. Mirrors Filter::process_sample. */
  initFilter(v, sr, keepState) {
    v.ftype = clamp(this.P(14, 1), 0, 4);
    v.res = clamp(this.P(20, 10), 0, 127) / 127;
    v.i0 = clamp(Math.floor(clamp(this.P(19, 64), 0, 127) * 1024 / 127), 0, 1023);
    v.sr = sr;
    v.slew_interval = Math.max(1, (sr / 20) | 0); v.slew_n = v.slew_interval;
    v.cache_idx = -1; v.cache_res = -1;
    v.slew_c = 1 - Math.exp(-1000 / sr);
    v.lpdl_sub = (sr <= 48000) ? 2 : 1;
    /* J (staged law): the CVcf leveler retention is 5 ms (core filter.cpp:59
     * FUN_18003a850: coef = 1 - exp(-1/(fs\u00b70.005))); the web 0.3 s half-life
     * let the leveler collapse 023-class peak-normalized signals. */
    v.levelerCoef = 1 - Math.exp(-1 / (sr * 0.005));
    var satX = clamp(this.P(23, 0), 0, 127) / 127;
    v.sat = satX * Math.exp(5.8 * (satX - 1));
    if (keepState) return;   // FUN_18003a780 note-on on a live voice: arm the
                             // fs/20 cutoff slew ONLY — the ladder states,
                             // cutoff position and leveler persist (zeroing
                             // them makes the LP24 ring from silence: a
                             // deeper attack transient than the device has)
    v.i_cur = v.i0; v.i_start = v.i0;
    v.live_init = false;
    v.g = v.A = v.rmin = v.K = v.s1 = v.s3 = 0;
    v.L0t = v.L1t = v.L2t = v.L0 = v.L1 = v.L2 = 0;
    v.q0 = v.q1 = v.q2 = v.q3 = 0; v.aP = v.bP = v.cP = v.dP = 0;
    v.kk = v.a1 = v.p2 = v.p3 = v.p4 = v.w2 = v.w3 = v.g4 = v.g5 = 0;
    v.c2 = v.c3 = v.c4 = 0;
    v.u1 = v.rprime = v.m = v.gq = v.nout = v.m4 = v.ls1 = v.ls2 = v.ls3 = v.m2 = 0;
    v.lev = 0;
  }

  updateFilterCutoff(v, extra, lfoCut) {
    var t = v.i0 + v.iKey + extra;
    var mm = lfoCut;
    var mirror = (mm > 0) ? (1024 - t) : t;
    var p = mirror * mm;
    t = t + ((p + ((p >> 31) & 0x3ff)) >> 10);
    if (t > 1023) t = 1023;
    if (t < 0) t = 0;
    if (t === v.i_cur || v.slew_n >= v.slew_interval) v.i_cur = t;
    else v.i_cur = (((t - v.i_start) * v.slew_n) / v.slew_interval | 0) + v.i_start;
    v.slew_n++;
  }

  setupFilterCore(v) {
    var hz = fcOfIndex(v.i_cur), sr = v.sr;
    if (v.ftype === 0 || v.ftype === 2 || v.ftype === 3) {
      v.g = 2 * Math.sin(Math.PI * hz / (2 * sr));
      v.rmin = v.res < 1 ? v.res : 1;
      v.A = 1 - 0.7 * v.rmin;
      v.K = v.rmin - 1;
    } else if (v.ftype === 4) {
      var fc = (1.5 * hz < 0.45 * sr) ? 1.5 * hz : 0.45 * sr;
      var T = Math.tanh(Math.PI * fc / (sr * v.lpdl_sub));
      v.kk = T / (2 * (1 + T));
      var r = 15 * v.res;
      v.a1 = 1 / (1 + T);
      var k2 = v.kk * v.kk;
      var A2 = 1 / (1 - k2);
      v.p2 = A2 * v.kk;
      v.w2 = k2 / (1 - k2);
      var d2 = (1 - k2) / (1 - 2 * k2);
      v.p3 = d2 * v.kk;
      var A3 = (1 - 2 * k2) / (1 - 3 * k2 + k2 * k2);
      v.p4 = 2 * v.kk * A3;
      v.c2 = A2 * v.a1; v.c3 = d2 * v.a1; v.c4 = A3 * v.a1;
      v.w3 = v.w2 * v.p3;
      v.g4 = 2 * v.kk / (1 - 2 * v.kk * v.p3);
      var t = Math.tanh(v.p3);
      v.u1 = 1 / (1 + t);
      v.g5 = 2 * t * v.u1;
      v.rprime = r * v.u1;
      v.m = 1 / (1 + v.rprime * v.w3 * v.g4);
      v.gq = T / (1 + T);
      v.nout = v.lpdl_sub * 0.65 * (1 + 3 * v.res);
    } else {
      var fcn = hz * 2 / sr;
      v.L0t = -1.6 * fcn * fcn + 3.6 * fcn - 1;
      v.L1t = (1 + v.L0t) * 0.5;
      /* M (staged law, staged_core_diff.md #4): core setup_lp24 L2t =
       * res·exp(LN2_BIN·(1 − (4.3·fcd − 1.6·fcd²))) — the 4-stage cascade
       * per-stage |H|@fc product (−5.2 dB at fc, cvcf_leveler_law addendum).
       * The web had the old 2.15/1.25 shortcut poly. */
      v.L2t = v.res * Math.exp(1.386249 * (1 - (4.3 * fcn - 1.6 * fcn * fcn)));
      if (!v.live_init) { v.L0 = v.L0t; v.L1 = v.L1t; v.L2 = v.L2t; v.live_init = true; }
    }
  }

  runFilterCore(v, x) {
    var y;
    if (v.ftype === 0 || v.ftype === 2 || v.ftype === 3) {
      var u = v.A * x;
      v.s1 += v.g * v.s3;
      v.s3 += v.g * ((u - v.s1) + v.K * v.s3);
      v.s1 += v.g * v.s3;
      /* FUN_180038300: the HP tap u2 is taken BEFORE the second s3 update,
       * and that update is s3 += g*u2 (computing u2 after yields u2*(1+K*g),
       * nulling HP12 at high fc). */
      var u2 = (u - v.s1) + v.K * v.s3;
      v.s3 += v.g * u2;
      y = (v.ftype === 2) ? u2 : (v.ftype === 3 ? v.s3 : v.s1);
      if (v.res > 0.9 && Math.abs(y) > 20) y = y > 0 ? 20 : -20;
    } else if (v.ftype === 4) {
      var xin0 = x, out = 0;
      for (var j = 0; j < v.lpdl_sub; j++) {
        var xin = (j === 0) ? xin0 : 0;
        var a = v.ls3 * v.a1;
        var b = v.ls2 * v.c2 + a * v.p2;
        var c = v.ls1 * v.c3 + b * v.p3;
        var d = v.m4 * v.c4 + c * v.p4;
        var fb = v.rprime * (a + b * v.kk + c * v.w2 + d * v.w3);
        var e = (xin - fb + v.m2 * v.u1) * v.m;
        var s = tanh3(e);
        d = 1.2857142857142858 * s * v.g4 + d;
        c = d * v.p3 + c;
        b = c * v.p2 + b;
        a = b * v.kk + a;
        v.ls1 = ((b + d) * 0.5 - v.ls1) * v.gq + c;
        v.ls2 = ((a + c) * 0.5 - v.ls2) * v.gq + b;
        v.ls3 = (b * 0.5 - v.ls3) * v.gq + a;
        v.m2 = v.m2 + (a * 15 * v.res - v.m2) * v.g5;
        v.m4 = ((c + 1.2857142857142858 * s) - v.m4) * v.gq + d;
        out = b * v.nout;
      }
      y = out;
    } else {
      var a2 = x - v.q3 * v.L2;
      var b2 = (a2 + v.aP) * v.L1 - v.q0 * v.L0;
      var c2 = (b2 + v.bP) * v.L1 - v.q1 * v.L0;
      var d2 = (c2 + v.cP) * v.L1 - v.q2 * v.L0;
      var e2 = (d2 + v.dP) * v.L1 - v.q3 * v.L0;
      /* M (staged law, staged_core_diff.md #3): the LP24 ±20 output limiter
       * is ALWAYS on (core run_lp24 FUN_10032a90: the res-gate bVar2 =
       * DAT_10064cb8(-1.07e8) < res is always true; DAT_10064528/90 =
       * ±20 in the CVcf domain). */
      if (Math.abs(e2) > 20) e2 = e2 > 0 ? 20 : -20;
      v.L0 += (v.L0t - v.L0) * v.slew_c;
      v.L1 += (v.L1t - v.L1) * v.slew_c;
      v.L2 += (v.L2t - v.L2) * v.slew_c;
      v.aP = a2; v.bP = b2; v.cP = c2; v.dP = d2;
      v.q0 = b2; v.q1 = c2; v.q2 = d2; v.q3 = e2;
      y = e2;
    }
    return y;
  }

  filterSample(v, x, extra, lfoCut) {
    this.updateFilterCutoff(v, extra, lfoCut);
    if (v.cache_idx !== v.i_cur || v.cache_res !== v.res) {
      v.cache_idx = v.i_cur; v.cache_res = v.res;
      this.setupFilterCore(v);
    }
    var y = this.runFilterCore(v, x);
    var v1 = Math.abs(y) - 1.1;
    if (v1 < 0) v1 = 0;
    v.lev += (v1 - v.lev) * v.levelerCoef;
    y = (1.1 / (v.lev + 1.1)) * y;
    if (v.sat !== 0) {
      var sa = 100 * v.sat;
      y = y * (1 + sa) / (1 + sa * Math.abs(y));
    }
    return y;
  }

  /* Block control plane, evaluated once per render quantum (the arp segment
   * loop reuses these statics across sub-segments; params are constant
   * within a block). Stored on the instance so no per-segment allocation. */
   prepareBlock(sr, N) {
     this._sr = sr;
     this._mg = this.masterGain();
    this._ampGain = ampGainCurve(clamp(this.P(29, 90), 0, 127));
    var ftype = clamp(this.P(14, 1), 0, 4);
    this._hp = (ftype === 2 || ftype === 3);
    this._wt = decodeWavetables();
    this._c1 = OSC1_CODE[clamp(this.P(0, 1), 0, 3)];
    this._c2 = OSC2_CODE[clamp(this.P(1, 1), 0, 3)];
    this._w1 = OSC1_WAVE[clamp(this.P(0, 1), 0, 3)];
    this._w2 = OSC2_WAVE[clamp(this.P(1, 1), 0, 3)];
    this._pulse1 = (this._c1 === 2);
    this._pulse2 = (this._c2 === 2);
    /* param 5 is the panel STEP (0..100 = round(raw·100/127)); the device mix
     * law is raw/127 (rawBand 5 maps step back to the raw band). */
    var mix = clamp(rawBand(5, clamp(this.P(5, 50), 0, 100)), 0, 127) / 127;
    var subAmp = clamp(this.P(95, 0), 0, 127) * 4 / 127;
    var gains = mixGains(mix, subAmp);
    var g1 = gains.g1, g2 = gains.g2, gsub = gains.gsub;
    /* osc2 sync + ring (osc_dispatch.cpp §6.5/§6.6, params 6/7) — computed
     * before the gain compensation (legion 2026-10-08: osc1 x0.5 is gated on
     * ring==0, kernel_map §4) */
    this._sync = this.P(6, 0) !== 0 ? 1 : 0;
    this._ring = this.P(7, 0) !== 0 ? 1 : 0;
    /* amplitude compensation (kernel_map.md 4) */
    if (this._pulse1 && !this._ring) g1 *= 0.5;
    if (this._c1 === 1) g1 *= 0.7316;   /* Q: legion saw normalization */
    if (this._pulse2 || this._w2 === 'noise') g2 *= 0.65;
    this._g1 = g1; this._g2 = g2; this._gsub = gsub; this._g2raw = gains.g2;
    this._subShape = SUB_WAVE[clamp(this.P(96, 1), 0, 3)];
    this._csub = SUB_CODE[clamp(this.P(96, 1), 0, 3)];
    this._subOct = this.P(97, 1) !== 0;

    /* pulse width + duty (param 8, pwMod from LFO dest 5 / mod env dest 2) */
    this._pw = clamp(this.P(8, 127), 0, 127) / 127;

    this._pbc = this.pbCents();
    this._modC = this.mod / 127 * 45;
    this._Q = this.filterQ();

    /* filter statics (FUN_180038070 / FUN_180038140) */
    this._i0 = clamp(Math.floor(clamp(this.P(19, 64), 0, 127) * 1024 / 127), 0, 1023);
    this._amt22 = clamp(this.P(22, 0), 0, 127) / 127;
    this._amt21 = filterAmount(clamp(this.P(21, 63), 0, 127));
    this._fltVelOn = clamp(this.P(24, 0), 0, 127) !== 0;
    var satP = clamp(this.P(23, 0), 0, 127);
    var satX = satP / 127;
    this._sat = satX * Math.exp(5.8 * (satX - 1));
    this._levelerCoef = 1 - Math.pow(0.5, 1 / (sr * 0.3));

    /* mod env amount / dest (params 11, 71) */
    var meAmt = modEnvAmount(clamp(this.P(11, 64), 0, 127));
    this._meSign = meAmt < 0 ? -1 : 1; this._meAbs = Math.abs(meAmt);
    this._meDest = clamp(this.P(71, 0), 0, 7);   /* Q: lfo.h DEST enum */
    this._fmBand = clamp(this.P(45, 0), 0, 127);
    this._fmRampMax = (sr / 1000) | 0;   // cv+0x160 = fmRampMax (≈44 @44.1k)


    /* LFO control plane (FUN_18003dbe0 / engine.cpp §13): sync params here;
     * the phase is advanced by the full block at the END of process()
     * (close_chunk: lfo_tick(lfo, chunk_done_)) so renderVoices reads the
     * LFO at (phase + off) mod period on the control-tick grid. */
    this.lfoSync(0); this.lfoSync(1);
  }

  portaAdvance(n) {
    for (var pi = 0; pi < this.voices.length; pi++) {
      var pg = this.voices[pi].porta;
      if (pg && pg.active) {
        pg.pos += n;
        if (pg.pos >= pg.dur) { pg.pos = 0; pg.remaining = 0; pg.active = 0; }
        else pg.remaining = (Math.exp(-4 * pg.pos / pg.dur) * (1 - pg.pos / pg.dur) * pg.delta) | 0;
      }
    }
  }

  /* Render every live voice over the sample window [from,to). Hot path:
   * no allocation inside the per-sample loop. */
  renderVoices(L, R, from, to) {
    var sr = sampleRate;
    var mg = this._mg, wt = this._wt;
    var c1 = this._c1, c2 = this._c2, csub = this._csub;
    var pulse1 = this._pulse1, pulse2 = this._pulse2;
    var g1 = this._g1, g2 = this._g2, gsub = this._gsub, g2raw = this._g2raw;
    var fmRampMax = this._fmRampMax;
    var subOct = this._subOct;
    var pw = this._pw, pbc = this._pbc, modC = this._modC;
    var i0 = this._i0, amt22 = this._amt22, amt21 = this._amt21;
    var meSign = this._meSign, meAbs = this._meAbs, meDest = this._meDest;
    var ampGain = this._ampGain;
    var ampGainF = Math.fround(ampGain);

    var keep = [];
    for (var vi = 0; vi < this.voices.length; vi++) {
      var v = this.voices[vi];
      /* env 4 = idle: the device voice keeps its oscillators/LFSR running
       * (free-run, spec_phase Branch B); eg is 0 so the output sums to zero. */
      /* CMixDevice per-voice pan law (FUN_180015a20): pan > 0 → gL = max(1−pan,1e-7),
       * gR = 1; pan < 0 mirrored; pan = 0 unity. Gives true stereo from the mixer. */
      var vpan = v.pan || 0, gl = 1, gr = 1;
      if (vpan > 0) gl = Math.max(1 - vpan, 1e-7);
      else if (vpan < 0) gr = Math.max(1 + vpan, 1e-7);
      var fr = this.oscFreqs(v.note, v.detuneCents);
      var f1 = fr.f1, f2 = fr.f2;
      var kbd2 = this.P(4, 1) !== 0;

      /* pitch modulation sums (voice.cpp FUN_18003dbe0 routing, FUN_18003b940
       * apply): the device sums in 1/128-OCTAVE units (bend, porta, LFO
       * dest1/2, mod env dest 0 scale 640) and applies f·2^(units/128),
       * clamped ±1280 units (= ±10 oct = ±12000 cents). */
      var mv = v.mv || (v.mv = mkModEnv());
      /* FM (voice.cpp FUN_18003bf50 / osc_dispatch §6.7): gate = LFO dest6
       * + signed mod-env dest1 (512 scale, per chunk); TARGET depth via the
       * pow(1000) law; CURRENT depth lives in the per-voice COSRAMP ramp
       * state machine (fmRampStep, mirrors core FmRampState per sample).
       * The 0.65 osc2 pulse/noise gain comp applies only while FM is idle:
       * FMactive = (depth != 0 || target != 0) AFTER the state machine, so
       * a ramping-down depth keeps the FM kernel. */
      var fm = v.fm || (v.fm = mkFmRamp());
      var fmIdleComp = pulse2 || this._w2 === 'noise';

      var ae = v.ae || (v.ae = mkAdsr(2048, true));
      var fe = v.fe || (v.fe = mkAdsr(1024, false));
      if (v.gCur === undefined) { v.gCur = 0; v.gStep = 0; v.fltLvl = 0; }
      v.ampChRem = 0; v.fltChRem = 0;  // core begin_block: chunks never span blocks
      var env = v.env, eg = v.eg;

      /* filter statics for this voice/block (FUN_180038070 / FUN_180038140) */
      v.iKey = keytrackIndex(i0, v.note, amt22);
      var amt21b = amt21;
      if (this._fltVelOn)
        amt21b = filterVelScale127(v.vel === undefined ? 127 : v.vel) * amt21 * (1 / 127);
      var amt = envHeadroom(i0, v.iKey, amt21b);
      var sign = amt < 0 ? -1 : 1;
      var amtScale = 1024 * Math.abs(amt);

      /* control-tick loop (engine.cpp render_sub / begin_control_tick,
       * spec_lfo_fx.md §13): the voice re-reads the LFO at (phase + off) mod
       * period on the CONTROL_TICK_FRAMES grid, cut at the LFO segment
       * boundaries (FUN_180014d10 segLen, minSegment-clamped); bands, duty
       * and the amp-mod term follow the tick's LFO value. */
      var pos = from;
      while (pos < to) {
        var segA = lfoSegRemaining(this.lfoState[0], pos);
        var segB = lfoSegRemaining(this.lfoState[1], pos);
        var tick = segA < segB ? segA : segB;
        var grid = 32 - ((this.absPos + pos) % 32);
        if (grid < tick) tick = grid;
        if (to - pos < tick) tick = to - pos;
        var lm = this._lfoMod || (this._lfoMod = { pitch: 0, pitch2: 0, cutoff: 0, amp: 0, pw: 0, pan: 0, fm: 0 });
        lm.pitch = 0; lm.pitch2 = 0; lm.cutoff = 0; lm.amp = 0; lm.pw = 0; lm.pan = 0; lm.fm = 0;
        this.lfoRoute(0, lm, pos);
        this.lfoRoute(1, lm, pos);
        /* P (staged law, 121/123/124): re-seed waves 3/4 at the end of
         * the tick whose samples cross the period, on the 32-sample
         * grid (core lfo_tick per control chunk). */
        for (var li2 = 0; li2 < 2; li2++) {
          var st2 = this.lfoState[li2];
          if (st2.onOff && st2.period > 0 && ((st2.wave - 3) >>> 0) < 2) {
            var pp0 = st2.phase + pos;
            var pp1 = pp0 + tick;
            if (pp0 <= st2.period && pp1 > st2.period) {
              st2.rndNext = st2.rndCur;
              st2.rndCur = lfoDrawSh(st2);
            }
          }
        }
        var cents = pbc + modC * Math.sin(2 * Math.PI * 5.5 * (this.time + pos / sr));
        var portaUnits = (v.porta && v.porta.active) ? v.porta.remaining : 0;
        var m1 = cents + portaUnits * 9.375 + lm.pitch * 9.375;
        m1 = clamp(m1, -12000, 12000);
        var curF1 = f1 * Math.pow(2, m1 / 1200); if (curF1 > 22000) curF1 = 22000;
        var inc1 = (curF1 * 134217728 / sr) | 0;
        var lfoPitch2 = (lm.pitch + lm.pitch2) * 9.375;
        var m2k = (kbd2 ? cents + portaUnits * 9.375 : 0) + lfoPitch2;
        /* band selection per tick from the modulated frequencies (§5.6) */
        var wt1 = waveTable(wt, c1, curF1);
        var wt2 = (c2 === 4) ? null : waveTable(wt, c2, f2 * Math.pow(2, m2k / 1200));
        var subShift = subOct ? 1 : 0;
        var wtSub = (gsub > 0) ? waveTable(wt, csub, subOct ? curF1 * 0.5 : curF1) : null;
        var duty32 = (pulse1 || pulse2) ? (pulseDutyIndex(pw, lm.pw) << 16) >>> 0 : 0;
        var ampModF = Math.fround(Math.fround(2048 - lm.amp) * (1 / 2048));
        var lfoCut = lm.cutoff;
        var tickEnd = pos + tick;

      for (var i = pos; i < tickEnd; i++) {
        /* mod env chunk walk (core step_env_chunks + env::ADSR): one level
         * per chunk applied to every sample of the chunk; chunks never span
         * the render range (next_chunk_len is capped by the block remainder). */
        if (mv.chRem === 0) {
          if (mv.stage !== 0) {
            var remS = tickEnd - i;
            var cl = modEnvNextChunk(mv, remS);
            if (cl < 1) cl = 1;
            mv.lvl = modEnvAdvance(mv, cl);
            mv.chRem = cl;
          } else {
            mv.lvl = 0;
            mv.chRem = (to - i) > 0 ? (to - i) : 1;
          }
        }
        var modLvl = mv.lvl;
        mv.chRem--;
        /* osc2 pitch: 1/128-oct sums (core gate FUN_18003b940 — the
         * increment is recomputed only when the sum changes) */
        var m2 = m2k + ((meDest === 1 || meDest === 2) ? meSign * modLvl * 9.375 : 0);
        m2 = clamp(m2, -12000, 12000);
        if (m2 !== v.pm2) {
          v.pm2 = m2;
          var cf2 = f2 * Math.pow(2, m2 / 1200); if (cf2 > 22000) cf2 = 22000;
          v.inc2 = (cf2 * 134217728 / sr) | 0;
        }
        var duty = duty32;
        if ((pulse1 || pulse2) && meDest === 5 && modLvl !== 0) {
          duty = (pulseDutyIndex(pw, lm.pw + meSign * modLvl) << 16) >>> 0;
        }
        var fmGate = lm.fm + (meDest === 6 ? meSign * modLvl : 0);
        if (fmGate !== v.fmGateP) {
          v.fmGateP = fmGate;
          v.fmTgt = fmDepthFromGate(this._fmBand, fmGate);
        }
        var fmTarget = v.fmTgt;
        /* §6.7: per-sample FM ramp step (the core runs the state machine +
         * block_cur advance once per render call, num_samples = 1). */
        var fmDepth = fmRampStep(fm, fmTarget, fmRampMax);
        var fmOn = (fmDepth !== 0) || (fmTarget !== 0);
        /* oscillator (osc_dispatch §6.1): osc2 term first, osc1 second, sub
         * third, then the 32-bit phase accumulators advance. FM-kernel
         * modulator amplitude (FUN_18004ade0/FUN_18004b180, legion 2026-10-07):
         * while FM is on the osc2 term is scaled in the kernel — LFSR noise
         * ±0.65 (DAT_180077418), pulse saw-difference ×0.5 (DAT_180072b60) —
         * and the scaled value feeds BOTH the audible osc2 term (the
         * dispatcher's ×0.65 idle comp is skipped) and the phase-mod term. */
        var s2;
        if (c2 === 4) {
          s2 = lfsrNext(v);
        } else {
          s2 = readTable(wt2, v.ph2);
          if (pulse2) {   /* Q: device RMS-norms the pulse to 0.42 */
            s2 -= readTable(wt2, (v.ph2 + duty) >>> 0);
            s2 *= 0.447;
          }
        }
        if (fmOn) { if (c2 === 4) s2 *= 0.65; else if (pulse2) s2 *= 0.5; }
        var s1 = readTable(wt1, v.ph1);
        if (pulse1) s1 -= readTable(wt1, (v.ph1 + duty) >>> 0);
        var g2v = (fmOn && fmIdleComp) ? g2raw : g2;
        var x = this._ring ? 0.5 * (g2v * s2 * s1 + g1 * s1) : (g1 * s1 + g2v * s2);
        if (wtSub) x += gsub * readTable(wtSub, (v.ph1 >>> subShift));
        var ph1n = (v.ph1 + inc1 + (fmOn ? ((fmDepth * s2) | 0) : 0)) >>> 0;
        var wrap = (ph1n & 0x7ffffff) < (v.ph1 & 0x7ffffff);
        v.ph1 = ph1n;
        if (c2 === 4) {
          /* noise (osc_dispatch §6.5, legion TASK1 reseed matrix 2026-10-08):
           * the accumulator is NOT advanced; the LFSR re-seeds to 10 on the
           * master cycle wrap ONLY in the sync kernels (12 audited sites all
           * in the sync!=0 branch); sync==0 noise kernels (incl. the FM
           * modulator) never re-seed. */
          if (wrap && this._sync) v.lfsr = 10;
        } else if (this._sync && wrap) {
          v.ph2 = Number((BigInt(v.ph1 & 0x7ffffff) * BigInt(v.inc2 | 0)) / BigInt(inc1 | 0)) >>> 0;
        } else {
          v.ph2 = (v.ph2 + v.inc2) >>> 0;
        }

        /* filter (CVcf): cutoff slew + core + leveler + soft-clip per sample */
        /* amp/filter env chunk walk (core Voice::step_env_chunks + env::ADSR):
         * CVca (half_chunks=1) advances its chunk at the block start / chunk
         * boundary and ramps the applied gain LINEARLY across the chunk
         * (g_step = (g_target − g_cur)/cl, g_cur += g_step per sample,
         * g_target = (amp/2048)·amp_gain·vel_factor·amp_mod in float32,
         * FUN_180037c30); CVcf (full chunks) holds its integer chunk level
         * (stair-step) and the cutoff slew (update_cutoff) smooths it. */
        if (v.ampChRem === 0) {
          var clA = adsrNextChunk(ae, tickEnd - i);
          if (clA < 1) clA = 1;
          var ampLvl = adsrAdvance(ae, clA);
          var gT = Math.fround(Math.fround(Math.fround(Math.fround(ampLvl) * (1 / 2048)) * ampGainF) * Math.fround(v.peak)) * ampModF;
          v.gStep = Math.fround((Math.fround(gT) - v.gCur) / clA);
          v.ampChRem = clA;
        }
        if (v.fltChRem === 0) {
          var clF = adsrNextChunk(fe, tickEnd - i);
          if (clF < 1) clF = 1;
          v.fltLvl = adsrAdvance(fe, clF);
          v.fltChRem = clF;
        }
        v.gCur = Math.fround(v.gCur + v.gStep);
        v.ampChRem--;
        v.fltChRem--;
        var extra = sign * v.fltLvl;
        var y = this.filterSample(v, x, extra, lfoCut);
        /* CVca end-of-release hook (FUN_180037f00): the amp env chunk walk
         * reaching IDLE (release done, incl. the half-chunk 0.9·total early
         * end) resets the FM ramp + mod env. */
        if (ae.stage === 0 && !v.held && env === 3) {
          fmReleaseReset(fm); modEnvReset(mv);
          this.initFilter(v, v.sr);   // core end-of-release: filt.reset()
        }
        env = ae.stage === 0 ? 4 : ae.stage - 1;
        eg = ae.cur * (1 / 2048);
        var o = y * v.gCur * mg;
        L[i] += o * gl;
        if (R !== L) R[i] += o * gr;
      }
        pos += tick;
      }
      v.eg = eg; v.env = env; v.aprog = ae.prog; v.offLevel = ae.off * (1 / 2048);
      v.feg = fe.cur * (1 / 1024); v.fenv = fe.stage === 0 ? 4 : fe.stage - 1;
      keep.push(v);   // device voices are persistent per slot (free-run pool)
    }
    this.voices = keep;
  }

  /* Engine block splitter (FUN_1800018f0 / render_range §13): cut the render
   * quantum exactly at every arp note-on (step boundary) and note-off
   * (gate-off edge), then advance the arp clock over each sub-segment. */
  renderArp(L, R, N) {
    var a = this.arp, pos = a.pos, step = a.stepLen;
    var segStart = 0, remaining = N;
    while (remaining > 0) {
      var d;
      if (pos === 0) {
        this.arpStepBoundary();
        var onLen = (step * a.gate) | 0;
        this.arpGateOffAt = (a.gate < 1.0 && onLen > 0) ? onLen : step;
        d = this.arpGateOffAt;
      } else if (this.arpNote !== -1 && pos === this.arpGateOffAt) {
        this.arpReleaseNote();
        d = step - pos;
      } else {
        var toStep = step - pos;
        var toGate = (this.arpNote !== -1) ? this.arpGateOffAt - pos : toStep;
        d = toGate < toStep ? toGate : toStep;
      }
      if (d > remaining) d = remaining;
      if (d <= 0) d = 1;                       // degenerate gate: never stall
      this.portaAdvance(d);
      this.renderVoices(L, R, segStart, segStart + d);
      this.arpAdvance(d);
      pos = a.pos;
      segStart += d;
      remaining -= d;
    }
  }

  /* Offline render entry (parity harness): mirrors portable-synth/render/
   * offline_render.cpp scheduling — events applied at their exact sample
   * offsets, control plane re-evaluated on the absolute CONTROL_TICK (32)
   * grid cut at event offsets, streaming FX per range. events: [{t:'param',
   * sample,id,value}, {t:'on',sample,note,vel}, {t:'off',sample,note}].
   * Returns {left,right} Float32Array(numFrames). */
  renderOffline(events, numFrames, sr, bs) {
    globalThis.sampleRate = sr;
    if (this.arp.sr !== sr) {
      this.arp.sr = sr; this.arpRecompute();
      this.chorusSetSampleRate(sr); this.delaySetSampleRate(sr);
    }
    var evs = events.slice().sort(function (a, b) { return a.sample - b.sample; });
    var L = new Float32Array(numFrames), R = new Float32Array(numFrames);
    var cuts = [0];
    for (var i = 0; i < evs.length; i++) {
      if (evs[i].sample > 0 && evs[i].sample < numFrames) cuts.push(evs[i].sample);
    }
    for (var s = bs; s < numFrames; s += bs) cuts.push(s);
    cuts.push(numFrames);
    cuts.sort(function (a, b) { return a - b; });
    var uc = [];
    for (var i = 0; i < cuts.length; i++) {
      if (i === 0 || cuts[i] !== cuts[i - 1]) uc.push(cuts[i]);
    }
    var ei = 0;
    var self = this;
    function applyAt(pos) {
      while (ei < evs.length && evs[ei].sample === pos) {
        var e = evs[ei++];
        if (e.t === 'param') self.handle({ t: 'p', id: e.id, v: e.value });
        else if (e.t === 'on') self.handleNoteOn(e.note, e.vel);
        else if (e.t === 'off') self.handleNoteOff(e.note);
      }
    }
    applyAt(0);
    var prev = 0;
    for (var ci = 1; ci < uc.length; ci++) {
      var c = uc[ci];
      if (c > prev) { self.process([], [[L.subarray(prev, c), R.subarray(prev, c)]]); prev = c; }
      applyAt(c);
    }
    if (prev < numFrames) self.process([], [[L.subarray(prev, numFrames), R.subarray(prev, numFrames)]]);
    return { left: L, right: R };
  }

  process(inputs, outputs) {
    var out = outputs[0];
    if (!out || out.length === 0) return true;
    var L = out[0], R = out.length > 1 ? out[1] : out[0];
    var sr = sampleRate, N = L.length;

    if (this.arp.sr !== sr) {
      this.arp.sr = sr; this.arpRecompute();
      this.chorusSetSampleRate(sr); this.delaySetSampleRate(sr);
    }
    this.prepareBlock(sr, N);
    if (this.arp.enabled) this.renderArp(L, R, N);
    else {
      /* voice blocks run on the device 32-sample control-tick grid (the engine
       * calls Voice::process_block once per tick; begin_block caps the env
       * chunks, porta advances at every commit_control_tick) */
      var ts = 0;
      while (ts < N) {
        var tn = N - ts; if (tn > 32) tn = 32;
        this.portaAdvance(tn);
        this.renderVoices(L, R, ts, ts + tn);
        ts += tn;
      }
    }
    if (R !== L) this.fxProcess(L, R, N);

    /* close_chunk (engine.cpp §13): the LFO phase + freq slew advance by the
     * whole block after the last tick is rendered. */
    lfoTick(this.lfoState[0], N);
    lfoTick(this.lfoState[1], N);

    this.absPos += N;
    this.time += N / sr;
    return true;
  }
}

if (typeof registerProcessor === 'function') {
  registerProcessor('synth1', Synth1Processor);
}
if (typeof module !== 'undefined' && module.exports) {
  /* expose the wavetable/filter helpers for the parity tests (static props) */
  Synth1Processor.decodeWavetables = decodeWavetables;
  Synth1Processor.selectBand = selectBand;
  Synth1Processor.readTable = readTable;
  Synth1Processor.waveTable = waveTable;
  Synth1Processor.bandThr = BAND_THR;
  Synth1Processor.bandHarmonics = BAND_HARM;
  Synth1Processor.lfsrNext = lfsrNext;
  Synth1Processor.tanh3 = tanh3;
  Synth1Processor.resetPhaseLcg = resetPhaseLcg;
  Synth1Processor.nextRandomPhase = nextRandomPhase;
  Synth1Processor.primePhaseLcg = primePhaseLcg;
  Synth1Processor.phaseLcgState = function () { return PHASE_LCG; };
  Synth1Processor.phaseOffsetTable = PHASE_T;
  Synth1Processor.mkLfo = mkLfo;
  Synth1Processor.lfoHz = lfoHz;
  Synth1Processor.lfoSpeedToHz = lfoSpeedToHz;
  Synth1Processor.lfoRange = lfoRange;
  Synth1Processor.lfoDepthToRange = lfoDepthToRange;
  Synth1Processor.lfoFreqSlew = lfoFreqSlew;
  Synth1Processor.lfoWaveform = lfoWaveform;
  Synth1Processor.lfoTick = lfoTick;
  Synth1Processor.lfoSetWave = lfoSetWave;
  Synth1Processor.lfoKeySync = lfoKeySync;
  Synth1Processor.lfoDrawSh = lfoDrawSh;
  Synth1Processor.lfoWave5Table = lfoWave5Table;
  Synth1Processor.lfoNoiseTable = lfoWave5Table;
  Synth1Processor.cosRampTable = cosRampTable;
  Synth1Processor.fmRampStep = fmRampStep;
  Synth1Processor.mkFmRamp = mkFmRamp;
  Synth1Processor.fmNoteOnReset = fmNoteOnReset;
  Synth1Processor.fmReleaseReset = fmReleaseReset;
  Synth1Processor.mkModEnv = mkModEnv;
  Synth1Processor.modEnvNoteOn = modEnvNoteOn;
  Synth1Processor.modEnvAdvance = modEnvAdvance;
  Synth1Processor.modEnvNextChunk = modEnvNextChunk;
  Synth1Processor.modEnvReset = modEnvReset;
  Synth1Processor.mkAdsr = mkAdsr;
  Synth1Processor.adsrTimes = adsrTimes;
  Synth1Processor.adsrSustain = adsrSustain;
  Synth1Processor.adsrAmount = adsrAmount;
  Synth1Processor.adsrNoteOn = adsrNoteOn;
  Synth1Processor.adsrNoteOff = adsrNoteOff;
  Synth1Processor.adsrReset = adsrReset;
  Synth1Processor.adsrNextChunk = adsrNextChunk;
  Synth1Processor.adsrAdvance = adsrAdvance;
  Synth1Processor.crtRand = crtRand;
  Synth1Processor.crtSrand = crtSrand;
  Synth1Processor.crtHoldrand = function () { return CRT_HOLDRAND; };
  module.exports = Synth1Processor;
}
