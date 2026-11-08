// ==UserScript==
// @name         YT Pitch Shifter
// @namespace    https://pitchshifter.local/
// @version      0.1.1
// @description  YouTube の再生中に、テンポを保ったままキーを ±6 半音（0.5 半音刻み）で変更します
// @match        https://m.youtube.com/*
// @match        https://www.youtube.com/*
// @run-at       document-end
// @inject-into  content
// @noframes
// @grant        none
// @homepageURL  https://github.com/ota09180426/PitchShifter
// @updateURL    https://raw.githubusercontent.com/ota09180426/PitchShifter/main/yt-pitch-shifter.user.js
// @downloadURL  https://raw.githubusercontent.com/ota09180426/PitchShifter/main/yt-pitch-shifter.user.js
// ==/UserScript==

(function () {
  'use strict';

  const CONFIG = {
    MIN: -6,              // 半音
    MAX: 6,               // 半音
    STEP: 0.5,            // 半音
    FFT_SIZE: 4096,       // 周波数分解能（大きいほど低音に強いが、遅延とアタックのにじみが増える）
    OVERLAP: 8,           // フレームの重なり数（大きいほど高音質・高負荷）
    SP_BUFFER: 4096,      // ScriptProcessor フォールバック時のバッファ長
    WORKLET_TIMEOUT_MS: 4000,
    POLL_MS: 500,
  };

  // ---DSP-START---
  /**
   * ステレオ・ピッチシフタ（テンポ維持）。
   * 位相ロック付きフェーズボコーダで、スペクトルのピーク単位で周波数方向に移動させる
   * （Laroche & Dolson 方式）。左右チャンネルには同じ位相回転をかけるため、定位が崩れない。
   * ratio が 1 のときは完全再構成（原音と同一、遅延のみ）。
   * このクラスは AudioWorklet にソースとして渡すため、外部の変数を参照してはならない。
   */
  class PitchShifterDSP {
    constructor(fftSize, overlap) {
      const N = fftSize || 4096;
      const H = N / (overlap || 8);
      const half = N >> 1;
      this.N = N;
      this.H = H;
      this.half = half;
      this.ratio = 1;
      this.semitones = 0;

      // 周期 Hann 窓（分析・合成の両方に使用）
      const win = new Float64Array(N);
      for (let i = 0; i < N; i++) win[i] = 0.5 - 0.5 * Math.cos((2 * Math.PI * i) / N);
      this.win = win;
      let wss = 0;
      for (let n = 0; n < H; n++) {
        let s = 0;
        for (let m = n; m < N; m += H) s += win[m] * win[m];
        wss += s;
      }
      wss /= H;
      this.outScale = 1 / (N * wss); // 逆FFTの 1/N と窓の重なり補正

      // FFT テーブル
      let bits = 0;
      while (1 << bits < N) bits++;
      this.rev = new Uint32Array(N);
      for (let i = 0; i < N; i++) {
        let r = 0;
        for (let b = 0; b < bits; b++) r |= ((i >> b) & 1) << (bits - 1 - b);
        this.rev[i] = r;
      }
      this.cosT = new Float64Array(half);
      this.sinT = new Float64Array(half);
      for (let i = 0; i < half; i++) {
        this.cosT[i] = Math.cos((2 * Math.PI * i) / N);
        this.sinT[i] = Math.sin((2 * Math.PI * i) / N);
      }

      this.re = new Float64Array(N);
      this.im = new Float64Array(N);
      const B = half + 1;
      this.xLr = new Float64Array(B);
      this.xLi = new Float64Array(B);
      this.xRr = new Float64Array(B);
      this.xRi = new Float64Array(B);
      this.yLr = new Float64Array(B);
      this.yLi = new Float64Array(B);
      this.yRr = new Float64Array(B);
      this.yRi = new Float64Array(B);
      this.mag = new Float64Array(B);
      this.phase = new Float64Array(B);
      this.prevPhase = new Float64Array(B);
      this.synPhase = new Float64Array(B);
      this.prevSynPhase = new Float64Array(B);
      this.peaks = new Int32Array(B);

      this.inL = new Float32Array(N);
      this.inR = new Float32Array(N);
      this.olaL = new Float64Array(N);
      this.olaR = new Float64Array(N);
      this.fifoSize = 1 << 16;
      this.fifoMask = this.fifoSize - 1;
      this.fifoL = new Float32Array(this.fifoSize);
      this.fifoR = new Float32Array(this.fifoSize);
      this.reset();
    }

    reset() {
      this.inL.fill(0);
      this.inR.fill(0);
      this.olaL.fill(0);
      this.olaR.fill(0);
      this.fifoL.fill(0);
      this.fifoR.fill(0);
      this.phase.fill(0);
      this.prevPhase.fill(0);
      this.synPhase.fill(0);
      this.prevSynPhase.fill(0);
      this.inPos = this.N - this.H;
      // 出力 FIFO に H サンプル分の無音を先に積んでおく（ブロック長が H 未満でも途切れないように）
      this.rd = 0;
      this.wr = this.H;
      this.count = this.H;
    }

    /** 入力から出力までの遅延（サンプル数） */
    get latency() {
      return this.N;
    }

    setSemitones(st) {
      this.semitones = st;
      this.ratio = Math.pow(2, st / 12);
    }

    /** inL/inR から n サンプル読み、outL/outR に n サンプル書く */
    process(inL, inR, outL, outR, n) {
      const N = this.N;
      const H = this.H;
      const bL = this.inL;
      const bR = this.inR;
      let pos = this.inPos;
      for (let i = 0; i < n; i++) {
        bL[pos] = inL[i];
        bR[pos] = inR[i];
        pos++;
        if (pos === N) {
          this._frame();
          bL.copyWithin(0, H);
          bR.copyWithin(0, H);
          pos = N - H;
        }
      }
      this.inPos = pos;

      const fL = this.fifoL;
      const fR = this.fifoR;
      const mask = this.fifoMask;
      let rd = this.rd;
      for (let i = 0; i < n; i++) {
        if (this.count > 0) {
          outL[i] = fL[rd];
          outR[i] = fR[rd];
          rd = (rd + 1) & mask;
          this.count--;
        } else {
          outL[i] = 0;
          outR[i] = 0;
        }
      }
      this.rd = rd;
    }

    _frame() {
      const N = this.N;
      const H = this.H;
      const half = this.half;
      const win = this.win;
      const re = this.re;
      const im = this.im;
      const bL = this.inL;
      const bR = this.inR;

      // L を実部、R を虚部に詰めて 1 回の複素 FFT で両チャンネルを変換
      for (let i = 0; i < N; i++) {
        const w = win[i];
        re[i] = bL[i] * w;
        im[i] = bR[i] * w;
      }
      this._fft(false);

      const xLr = this.xLr, xLi = this.xLi, xRr = this.xRr, xRi = this.xRi;
      const phase = this.phase;
      for (let k = 0; k <= half; k++) {
        const nk = (N - k) & (N - 1);
        const zr = re[k], zi = im[k];
        const cr = re[nk], ci = -im[nk];
        const Lr = (zr + cr) * 0.5, Li = (zi + ci) * 0.5;
        const Rr = (zi - ci) * 0.5, Ri = -(zr - cr) * 0.5;
        xLr[k] = Lr;
        xLi[k] = Li;
        xRr[k] = Rr;
        xRi[k] = Ri;
        phase[k] = Math.atan2(Li + Ri, Lr + Rr);
      }

      if (Math.abs(this.ratio - 1) < 1e-9) {
        // バイパス: re/im は未加工のスペクトルのまま。位相状態だけ同期しておく。
        this.synPhase.set(phase);
      } else {
        this._shift();
        const yLr = this.yLr, yLi = this.yLi, yRr = this.yRr, yRi = this.yRi;
        yLi[0] = 0; yRi[0] = 0; yLi[half] = 0; yRi[half] = 0;
        for (let k = 0; k <= half; k++) {
          re[k] = yLr[k] - yRi[k];
          im[k] = yLi[k] + yRr[k];
        }
        for (let k = 1; k < half; k++) {
          re[N - k] = yLr[k] + yRi[k];
          im[N - k] = yRr[k] - yLi[k];
        }
      }

      let t = this.prevPhase;
      this.prevPhase = this.phase;
      this.phase = t;
      t = this.prevSynPhase;
      this.prevSynPhase = this.synPhase;
      this.synPhase = t;

      this._fft(true);

      const s = this.outScale;
      const oL = this.olaL;
      const oR = this.olaR;
      for (let i = 0; i < N; i++) {
        const w = win[i] * s;
        oL[i] += re[i] * w;
        oR[i] += im[i] * w;
      }

      const fL = this.fifoL;
      const fR = this.fifoR;
      const mask = this.fifoMask;
      let wr = this.wr;
      for (let i = 0; i < H; i++) {
        fL[wr] = oL[i];
        fR[wr] = oR[i];
        wr = (wr + 1) & mask;
      }
      this.wr = wr;
      this.count += H;
      oL.copyWithin(0, H);
      oR.copyWithin(0, H);
      oL.fill(0, N - H);
      oR.fill(0, N - H);
    }

    _shift() {
      const N = this.N;
      const H = this.H;
      const half = this.half;
      const ratio = this.ratio;
      const TWO_PI = 2 * Math.PI;
      const xLr = this.xLr, xLi = this.xLi, xRr = this.xRr, xRi = this.xRi;
      const yLr = this.yLr, yLi = this.yLi, yRr = this.yRr, yRi = this.yRi;
      const mag = this.mag;
      const phase = this.phase;
      const prevPhase = this.prevPhase;
      const synPhase = this.synPhase;
      const prevSynPhase = this.prevSynPhase;
      const peaks = this.peaks;
      const binAdv = (TWO_PI * H) / N; // ビン中心周波数の 1 ホップあたり位相進み（ビン 1 つ分）

      let maxMag = 0;
      for (let k = 0; k <= half; k++) {
        const m =
          Math.sqrt(xLr[k] * xLr[k] + xLi[k] * xLi[k]) +
          Math.sqrt(xRr[k] * xRr[k] + xRi[k] * xRi[k]);
        mag[k] = m;
        if (m > maxMag) maxMag = m;
        // どのピークにも割り当てられなかったビン用の既定値
        const p = prevSynPhase[k] + binAdv * k;
        synPhase[k] = p - TWO_PI * Math.round(p / TWO_PI);
      }
      yLr.fill(0);
      yLi.fill(0);
      yRr.fill(0);
      yRi.fill(0);

      const thresh = Math.max(maxMag * 1e-5, 1e-12);
      let np = 0;
      for (let k = 2; k < half - 1; k++) {
        const m = mag[k];
        if (m > thresh && m > mag[k - 1] && m >= mag[k + 1] && m > mag[k - 2] && m >= mag[k + 2]) {
          peaks[np++] = k;
        }
      }
      if (np === 0) return;

      for (let j = 0; j < np; j++) {
        const p = peaks[j];
        const q = Math.round(p * ratio);
        if (q > half) break; // 以降のピークもすべて範囲外
        const start = j === 0 ? 0 : ((peaks[j - 1] + p) >> 1) + 1;
        const end = j === np - 1 ? half : (p + peaks[j + 1]) >> 1;

        // ピークの真の周波数（1 ホップあたりの位相進み）を前フレームとの位相差から推定
        let dev = phase[p] - prevPhase[p] - binAdv * p;
        dev -= TWO_PI * Math.round(dev / TWO_PI);
        const omega = binAdv * p + dev;

        // 移動先ビンでの合成位相 = 前フレームの合成位相 + 移動後の周波数ぶんの進み
        let rot = prevSynPhase[q] + omega * ratio - phase[p];
        rot -= TWO_PI * Math.round(rot / TWO_PI);
        const c = Math.cos(rot);
        const s = Math.sin(rot);
        const shift = q - p;

        let k0 = start;
        let k1 = end;
        if (k0 + shift < 0) k0 = -shift;
        if (k1 + shift > half) k1 = half - shift;
        for (let k = k0; k <= k1; k++) {
          const tb = k + shift;
          const a = xLr[k], b = xLi[k];
          yLr[tb] += a * c - b * s;
          yLi[tb] += a * s + b * c;
          const d = xRr[k], e = xRi[k];
          yRr[tb] += d * c - e * s;
          yRi[tb] += d * s + e * c;
          synPhase[tb] = phase[k] + rot;
        }
      }
    }

    _fft(inverse) {
      const N = this.N;
      const re = this.re;
      const im = this.im;
      const rev = this.rev;
      const cosT = this.cosT;
      const sinT = this.sinT;
      for (let i = 0; i < N; i++) {
        const j = rev[i];
        if (j > i) {
          let t = re[i]; re[i] = re[j]; re[j] = t;
          t = im[i]; im[i] = im[j]; im[j] = t;
        }
      }
      const sign = inverse ? 1 : -1;
      for (let size = 2; size <= N; size <<= 1) {
        const hs = size >> 1;
        const step = N / size;
        for (let i = 0; i < N; i += size) {
          for (let j = 0, k = 0; j < hs; j++, k += step) {
            const wr = cosT[k];
            const wi = sign * sinT[k];
            const a = i + j;
            const b = a + hs;
            const tr = re[b] * wr - im[b] * wi;
            const ti = re[b] * wi + im[b] * wr;
            re[b] = re[a] - tr;
            im[b] = im[a] - ti;
            re[a] += tr;
            im[a] += ti;
          }
        }
      }
    }
  }
  // ---DSP-END---

  // テスト用: DSP だけを公開して終了
  if (typeof window !== 'undefined' && window.__PS_TEST__ === 'dsp') {
    window.PitchShifterDSP = PitchShifterDSP;
    return;
  }
  if (window.top !== window.self) return;
  if (window.__ytPitchShifterLoaded) return;
  window.__ytPitchShifterLoaded = true;

  const LOG = '[YT Pitch Shifter]';
  const VERSION = '0.1.1';
  const WORKLET_NAME = 'yt-pitch-shifter-v1';

  function buildWorkletSource() {
    return (
      PitchShifterDSP.toString() +
      `
class YTPitchShifterProcessor extends AudioWorkletProcessor {
  constructor(options) {
    super();
    const o = (options && options.processorOptions) || {};
    this.dsp = new PitchShifterDSP(o.fftSize, o.overlap);
    this.zero = new Float32Array(128);
    this.scratch = new Float32Array(128);
    this.peak = 0;
    this.count = 0;
    this.port.onmessage = (e) => {
      const d = e.data || {};
      if (d.type === 'semitones') this.dsp.setSemitones(d.value);
    };
  }
  process(inputs, outputs) {
    const input = inputs[0] || [];
    const output = outputs[0];
    const oL = output && output[0];
    if (!oL) return true;
    const n = oL.length;
    if (this.zero.length < n) { this.zero = new Float32Array(n); this.scratch = new Float32Array(n); }
    const iL = input[0] || this.zero;
    const iR = input[1] || iL;
    const oR = output[1] || this.scratch;
    this.dsp.process(iL, iR, oL, oR, n);
    let pk = this.peak;
    for (let i = 0; i < n; i++) {
      const a = Math.abs(iL[i]); if (a > pk) pk = a;
      const b = Math.abs(iR[i]); if (b > pk) pk = b;
    }
    this.peak = pk;
    this.count += n;
    if (this.count >= sampleRate / 2) {
      this.port.postMessage({ type: 'level', peak: this.peak, st: this.dsp.semitones });
      this.peak = 0;
      this.count = 0;
    }
    return true;
  }
}
registerProcessor('${WORKLET_NAME}', YTPitchShifterProcessor);
`
    );
  }

  function withTimeout(promise, ms) {
    return new Promise((resolve, reject) => {
      const t = setTimeout(() => reject(new Error('timeout')), ms);
      promise.then(
        (v) => { clearTimeout(t); resolve(v); },
        (e) => { clearTimeout(t); reject(e); }
      );
    });
  }

  // ---------------------------------------------------------------------------
  // 音声エンジン
  // ---------------------------------------------------------------------------
  class AudioEngine {
    constructor() {
      this.ctx = null;
      this.node = null;
      this.spDSP = null;
      this.mode = 'idle'; // idle | loading | worklet | script
      this.semitones = 0;
      this.wantAttach = false; // 一度でも 0 以外にしたら true（以降は動画を処理経路に接続する）
      this.attached = new WeakSet();
      this.video = null;
      this.initPromise = null;
      this.error = '';
      this.silent = false;
      this.silentCount = 0;
      this.lastPeak = null;
      this.procSemitones = null;
      this.outputMuted = false;
      this.listeners = new Set();
    }

    on(fn) {
      this.listeners.add(fn);
    }

    emit() {
      for (const fn of this.listeners) {
        try { fn(); } catch (e) { console.error(LOG, e); }
      }
    }

    /** ユーザー操作（タップ等）のイベントハンドラから同期的に呼ぶこと。何度呼んでもよい。 */
    unlock() {
      try {
        if (!this.ctx) {
          try {
            // iPhone のマナーモード（消音スイッチ）中でも Web Audio が鳴るようにする（iOS 16.4+）
            if (navigator.audioSession) navigator.audioSession.type = 'playback';
          } catch (e) { /* noop */ }
          const AC = window.AudioContext || window.webkitAudioContext;
          if (!AC) {
            this.error = 'このブラウザは Web Audio に対応していません';
            this.emit();
            return;
          }
          try {
            this.ctx = new AC({ latencyHint: 'playback' });
          } catch (e) {
            this.ctx = new AC();
          }
          this.ctx.onstatechange = () => {
            this.emit();
            this._maybeAttach();
          };
        }
        this.resume();
        if (!this.initPromise) {
          this.mode = 'loading';
          this.initPromise = this._initGraph().catch((e) => {
            this.error = '初期化に失敗しました: ' + ((e && e.message) || e);
            console.error(LOG, e);
            this.emit();
          });
        }
      } catch (e) {
        this.error = String((e && e.message) || e);
        console.error(LOG, e);
        this.emit();
      }
    }

    resume() {
      const ctx = this.ctx;
      if (ctx && ctx.state !== 'running' && ctx.state !== 'closed') {
        try {
          const p = ctx.resume();
          if (p && p.catch) p.catch(() => {});
        } catch (e) { /* noop */ }
      }
    }

    async _initGraph() {
      const ctx = this.ctx;
      try {
        if (!ctx.audioWorklet || typeof AudioWorkletNode === 'undefined') {
          throw new Error('AudioWorklet unavailable');
        }
        const url = URL.createObjectURL(new Blob([buildWorkletSource()], { type: 'text/javascript' }));
        try {
          await withTimeout(ctx.audioWorklet.addModule(url), CONFIG.WORKLET_TIMEOUT_MS);
        } finally {
          URL.revokeObjectURL(url);
        }
        const node = new AudioWorkletNode(ctx, WORKLET_NAME, {
          numberOfInputs: 1,
          numberOfOutputs: 1,
          outputChannelCount: [2],
          channelCount: 2,
          channelCountMode: 'explicit',
          channelInterpretation: 'speakers',
          processorOptions: { fftSize: CONFIG.FFT_SIZE, overlap: CONFIG.OVERLAP },
        });
        node.port.onmessage = (e) => {
          const d = e.data;
          if (d && d.type === 'level') this._onLevel(d.peak, d.st);
        };
        node.onprocessorerror = () => {
          this.error = '音声処理でエラーが発生しました。ページを再読み込みしてください。';
          this.emit();
        };
        this.node = node;
        this.mode = 'worklet';
      } catch (err) {
        this.fallbackReason = String((err && err.message) || err);
        console.warn(LOG, 'AudioWorklet が使えないため ScriptProcessor で動作します:', err);
        const dsp = new PitchShifterDSP(CONFIG.FFT_SIZE, CONFIG.OVERLAP);
        const sp = ctx.createScriptProcessor(CONFIG.SP_BUFFER, 2, 2);
        let peak = 0;
        let count = 0;
        sp.onaudioprocess = (e) => {
          const ib = e.inputBuffer;
          const ob = e.outputBuffer;
          const iL = ib.getChannelData(0);
          const iR = ib.numberOfChannels > 1 ? ib.getChannelData(1) : iL;
          const n = ob.length;
          dsp.process(iL, iR, ob.getChannelData(0), ob.getChannelData(1), n);
          for (let i = 0; i < n; i++) {
            const a = Math.abs(iL[i]); if (a > peak) peak = a;
            const b = Math.abs(iR[i]); if (b > peak) peak = b;
          }
          count += n;
          if (count >= ctx.sampleRate / 2) {
            this._onLevel(peak, dsp.semitones);
            peak = 0;
            count = 0;
          }
        };
        this.spDSP = dsp;
        this.node = sp;
        this.mode = 'script';
      }
      this.node.connect(ctx.destination);
      this._applySemitones();
      this.emit();
      this._maybeAttach();
    }

    setSemitones(v) {
      this.semitones = v;
      if (v !== 0) this.wantAttach = true;
      this._applySemitones();
      this._maybeAttach();
    }

    _applySemitones() {
      if (this.mode === 'worklet') this.node.port.postMessage({ type: 'semitones', value: this.semitones });
      else if (this.mode === 'script') this.spDSP.setSemitones(this.semitones);
    }

    setVideo(video) {
      if (video === this.video) return;
      this.video = video;
      this.silentCount = 0;
      this.silent = false;
      this._maybeAttach();
      this.emit();
    }

    isAttached() {
      return !!(this.video && this.attached.has(this.video));
    }

    _maybeAttach() {
      const v = this.video;
      const ctx = this.ctx;
      if (!this.wantAttach || !v || !this.node || !ctx || ctx.state !== 'running') return;
      if (this.attached.has(v)) return;
      try {
        const src = ctx.createMediaElementSource(v);
        src.connect(this.node);
        this.attached.add(v);
        v.addEventListener('play', () => this.resume());
        console.info(LOG, 'video を接続しました', this.srcType());
        this.emit();
      } catch (e) {
        this.error = '動画の音声に接続できませんでした: ' + ((e && e.message) || e);
        console.error(LOG, e);
        this.emit();
      }
    }

    /** 診断用: 処理後の音を出力から切り離す／戻す */
    setOutputMuted(muted) {
      if (!this.node || !this.ctx || muted === this.outputMuted) return;
      try {
        if (muted) this.node.disconnect(this.ctx.destination);
        else this.node.connect(this.ctx.destination);
        this.outputMuted = muted;
      } catch (e) {
        console.error(LOG, e);
      }
      this.emit();
    }

    /** 診断用: Web Audio から直接ビープ音を鳴らす */
    testTone() {
      this.unlock();
      const ctx = this.ctx;
      if (!ctx) return;
      const t = ctx.currentTime + 0.02;
      const o = ctx.createOscillator();
      const g = ctx.createGain();
      o.frequency.value = 880;
      g.gain.setValueAtTime(0.0001, t);
      g.gain.exponentialRampToValueAtTime(0.25, t + 0.02);
      g.gain.exponentialRampToValueAtTime(0.0001, t + 0.5);
      o.connect(g);
      g.connect(ctx.destination);
      o.start(t);
      o.stop(t + 0.55);
    }

    _onLevel(peak, st) {
      this.lastPeak = peak;
      this.procSemitones = st;
      this.emit();
      const v = this.video;
      const playing =
        v && this.attached.has(v) && !v.paused && !v.muted && v.volume > 0 && v.readyState >= 3;
      this.silentCount = playing && peak === 0 ? this.silentCount + 1 : 0;
      const silent = this.silentCount >= 8; // 約 4 秒
      if (silent !== this.silent) {
        this.silent = silent;
        this.emit();
      }
    }

    srcType() {
      const v = this.video;
      if (!v) return '-';
      const s = v.currentSrc || v.src || '';
      if (s.startsWith('blob:')) return 'MSE';
      if (/m3u8|manifest/i.test(s)) return 'HLS';
      return s ? 'URL' : '-';
    }
  }

  // ---------------------------------------------------------------------------
  // UI
  // ---------------------------------------------------------------------------
  const CSS = `
:host { all: initial; }
* {
  box-sizing: border-box;
  font-family: -apple-system, BlinkMacSystemFont, "Hiragino Sans", "Segoe UI", sans-serif;
  -webkit-tap-highlight-color: transparent;
  -webkit-user-select: none;
  user-select: none;
}
button { -webkit-appearance: none; appearance: none; margin: 0; cursor: pointer; }
.fab {
  position: fixed;
  right: 12px;
  bottom: calc(84px + env(safe-area-inset-bottom, 0px));
  z-index: 2147483647;
  min-width: 52px;
  height: 52px;
  padding: 0 14px;
  border: none;
  border-radius: 26px;
  background: rgba(28, 28, 30, 0.88);
  color: #fff;
  font-size: 17px;
  font-weight: 700;
  font-variant-numeric: tabular-nums;
  box-shadow: 0 4px 14px rgba(0, 0, 0, 0.35);
  touch-action: manipulation;
}
.fab.active { background: #0a84ff; }
.fab.warn { background: #ff9f0a; color: #000; }
.panel {
  position: fixed;
  left: 12px;
  right: 12px;
  margin-left: auto;
  max-width: 380px;
  bottom: calc(146px + env(safe-area-inset-bottom, 0px));
  z-index: 2147483647;
  padding: 12px 16px 12px;
  border-radius: 18px;
  background: rgba(28, 28, 30, 0.96);
  color: #fff;
  box-shadow: 0 8px 30px rgba(0, 0, 0, 0.45);
}
.panel[hidden] { display: none; }
.head { display: flex; align-items: center; justify-content: space-between; }
.title { font-size: 13px; color: #aeaeb2; }
.close {
  width: 36px; height: 36px;
  border: none; border-radius: 18px;
  background: rgba(255, 255, 255, 0.12);
  color: #fff; font-size: 16px;
}
.value {
  margin: 0 0 4px;
  text-align: center;
  font-size: 34px;
  font-weight: 700;
  font-variant-numeric: tabular-nums;
}
.value small { margin-left: 4px; font-size: 14px; font-weight: 500; color: #aeaeb2; }
.slider { position: relative; height: 44px; margin: 0 14px; touch-action: none; }
.track {
  position: absolute; left: 0; right: 0; top: 20px; height: 4px;
  border-radius: 2px; background: rgba(255, 255, 255, 0.25);
}
.fill { position: absolute; top: 20px; height: 4px; border-radius: 2px; background: #0a84ff; }
.thumb {
  position: absolute; top: 8px; width: 28px; height: 28px; margin-left: -14px;
  border-radius: 14px; background: #fff; box-shadow: 0 2px 6px rgba(0, 0, 0, 0.4);
}
.ticks { position: relative; height: 22px; margin: 0 14px; }
.tick { position: absolute; top: 0; width: 1px; height: 5px; background: rgba(255, 255, 255, 0.35); }
.tick.major { height: 8px; background: rgba(255, 255, 255, 0.65); }
.label { position: absolute; top: 9px; transform: translateX(-50%); font-size: 11px; color: #aeaeb2; }
.buttons { display: flex; gap: 10px; margin-top: 6px; }
.buttons button {
  flex: 1; height: 50px;
  border: none; border-radius: 12px;
  background: rgba(255, 255, 255, 0.14);
  color: #fff; font-size: 24px; font-weight: 600;
  touch-action: manipulation;
}
.buttons button:active { background: rgba(255, 255, 255, 0.3); }
.buttons button:disabled { opacity: 0.35; }
.buttons .reset { font-size: 17px; }
.msg { margin-top: 10px; font-size: 12px; line-height: 1.45; color: #ffd60a; }
.msg:empty { display: none; }
.status { margin-top: 6px; font-size: 10px; color: #8e8e93; text-align: right; }
.diag { margin-top: 8px; padding-top: 8px; border-top: 1px solid rgba(255, 255, 255, 0.12); }
.diag-text { font-size: 11px; color: #aeaeb2; font-variant-numeric: tabular-nums; }
.diag-btns { display: flex; gap: 8px; margin-top: 6px; }
.diag-btns button {
  flex: 1; height: 36px;
  border: none; border-radius: 10px;
  background: rgba(255, 255, 255, 0.1);
  color: #fff; font-size: 13px;
  touch-action: manipulation;
}
.diag-btns button.on { background: #ff453a; }
`;

  function fmt(v) {
    if (v === 0) return '±0';
    return (v > 0 ? '+' : '−') + Math.abs(v).toFixed(1);
  }

  function el(tag, cls, text) {
    const e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text != null) e.textContent = text;
    return e;
  }

  class PitchUI {
    constructor(engine) {
      this.engine = engine;
      this.value = 0;
      this.dragging = false;

      const host = document.createElement('div');
      host.id = 'yt-pitch-shifter-host';
      host.style.cssText = 'all: initial; position: fixed; top: 0; left: 0; width: 0; height: 0; z-index: 2147483647;';
      const root = host.attachShadow({ mode: 'open' });
      const style = document.createElement('style');
      style.textContent = CSS;
      root.appendChild(style);

      // 浮きボタン
      this.fab = el('button', 'fab');
      this.fab.type = 'button';
      this.fab.setAttribute('aria-label', 'キー変更パネルを開く');

      // パネル
      this.panel = el('div', 'panel');
      this.panel.hidden = true;
      const head = el('div', 'head');
      const closeBtn = el('button', 'close', '✕');
      closeBtn.type = 'button';
      closeBtn.setAttribute('aria-label', '閉じる');
      head.append(el('span', 'title', 'キー（半音）'), closeBtn);
      this.valueEl = el('div', 'value');

      this.slider = el('div', 'slider');
      this.slider.setAttribute('role', 'slider');
      this.slider.setAttribute('aria-valuemin', String(CONFIG.MIN));
      this.slider.setAttribute('aria-valuemax', String(CONFIG.MAX));
      this.fill = el('div', 'fill');
      this.thumb = el('div', 'thumb');
      this.slider.append(el('div', 'track'), this.fill, this.thumb);

      const ticks = el('div', 'ticks');
      for (let i = CONFIG.MIN; i <= CONFIG.MAX; i++) {
        const pct = this._pct(i);
        const major = i % 3 === 0;
        const tk = el('div', major ? 'tick major' : 'tick');
        tk.style.left = pct + '%';
        ticks.appendChild(tk);
        if (major) {
          const lb = el('div', 'label', i === 0 ? '0' : (i > 0 ? '+' : '−') + Math.abs(i));
          lb.style.left = pct + '%';
          ticks.appendChild(lb);
        }
      }

      const buttons = el('div', 'buttons');
      this.minusBtn = el('button', 'minus', '−');
      this.resetBtn = el('button', 'reset', '0 に戻す');
      this.plusBtn = el('button', 'plus', '+');
      for (const b of [this.minusBtn, this.resetBtn, this.plusBtn]) b.type = 'button';
      this.minusBtn.setAttribute('aria-label', '0.5 半音下げる');
      this.plusBtn.setAttribute('aria-label', '0.5 半音上げる');
      buttons.append(this.minusBtn, this.resetBtn, this.plusBtn);

      this.msgEl = el('div', 'msg');
      this.statusEl = el('div', 'status');

      // 診断（実機での不具合調査用）
      const diag = el('div', 'diag');
      this.diagText = el('div', 'diag-text');
      const diagBtns = el('div', 'diag-btns');
      this.muteBtn = el('button', 'mute', '処理音を消す');
      this.toneBtn = el('button', 'tone', 'テスト音');
      this.muteBtn.type = 'button';
      this.toneBtn.type = 'button';
      diagBtns.append(this.muteBtn, this.toneBtn);
      diag.append(this.diagText, diagBtns);

      this.panel.append(head, this.valueEl, this.slider, ticks, buttons, this.msgEl, this.statusEl, diag);
      root.append(this.fab, this.panel);
      this.host = host;

      // --- イベント ---
      // YouTube 側のハンドラに操作が伝わらないようにする
      for (const type of ['click', 'pointerdown', 'pointerup', 'touchstart', 'touchend', 'mousedown', 'mouseup']) {
        host.addEventListener(type, (e) => e.stopPropagation());
      }
      // パネル上のどこをタップしても音声を再開できるように（iOS のオーディオ制限対策）
      const unlock = () => this.engine.unlock();
      this.panel.addEventListener('touchend', unlock, { passive: true });
      this.panel.addEventListener('click', unlock);

      this.fab.addEventListener('click', () => {
        this.engine.unlock();
        this.panel.hidden = !this.panel.hidden;
        this.render();
      });
      closeBtn.addEventListener('click', () => {
        this.panel.hidden = true;
        this.render();
      });
      this.minusBtn.addEventListener('click', () => this.setValue(this.value - CONFIG.STEP));
      this.plusBtn.addEventListener('click', () => this.setValue(this.value + CONFIG.STEP));
      this.resetBtn.addEventListener('click', () => this.setValue(0));
      this.muteBtn.addEventListener('click', () => this.engine.setOutputMuted(!this.engine.outputMuted));
      this.toneBtn.addEventListener('click', () => this.engine.testTone());

      const valueFromX = (x) => {
        const r = this.slider.getBoundingClientRect();
        const t = Math.min(1, Math.max(0, (x - r.left) / r.width));
        return CONFIG.MIN + t * (CONFIG.MAX - CONFIG.MIN);
      };
      this.slider.addEventListener('pointerdown', (e) => {
        this.engine.unlock();
        this.dragging = true;
        try { this.slider.setPointerCapture(e.pointerId); } catch (err) { /* noop */ }
        this.setValue(valueFromX(e.clientX));
        e.preventDefault();
      });
      this.slider.addEventListener('pointermove', (e) => {
        if (!this.dragging) return;
        this.setValue(valueFromX(e.clientX));
        e.preventDefault();
      });
      const endDrag = () => {
        if (!this.dragging) return;
        this.dragging = false;
        this.engine.unlock();
      };
      this.slider.addEventListener('pointerup', endDrag);
      this.slider.addEventListener('pointercancel', endDrag);

      engine.on(() => this.render());
      this.render();
    }

    mount() {
      if (!this.host.isConnected) (document.body || document.documentElement).appendChild(this.host);
    }

    _pct(v) {
      return ((v - CONFIG.MIN) / (CONFIG.MAX - CONFIG.MIN)) * 100;
    }

    setValue(v) {
      v = Math.round(v / CONFIG.STEP) * CONFIG.STEP;
      v = Math.min(CONFIG.MAX, Math.max(CONFIG.MIN, v));
      v = Math.round(v * 100) / 100 + 0; // 浮動小数点の誤差と -0 を除去
      if (v === this.value) return;
      this.value = v;
      this.engine.setSemitones(v);
      this.render();
    }

    _message() {
      const e = this.engine;
      if (e.error) return e.error;
      if (e.wantAttach && e.ctx && e.ctx.state !== 'running') {
        return '音声が一時停止しています。このパネルをタップすると再開します。';
      }
      if (e.silent) {
        return '動画の音声を取得できていない可能性があります（無音の区間なら無視してください）。音が出ない場合はページを再読み込みしてください。';
      }
      return '';
    }

    render() {
      const v = this.value;
      const msg = this._message();
      const txt = fmt(v);

      this.fab.textContent = v === 0 ? '♭♯' : txt;
      this.fab.classList.toggle('active', v !== 0 && !msg);
      this.fab.classList.toggle('warn', !!msg);

      if (this.panel.hidden) return;

      this.valueEl.replaceChildren(document.createTextNode(txt), el('small', null, '半音'));
      const pct = this._pct(v);
      const zero = this._pct(0);
      this.thumb.style.left = pct + '%';
      this.fill.style.left = Math.min(pct, zero) + '%';
      this.fill.style.width = Math.abs(pct - zero) + '%';
      this.slider.setAttribute('aria-valuenow', String(v));
      this.minusBtn.disabled = v <= CONFIG.MIN;
      this.plusBtn.disabled = v >= CONFIG.MAX;
      this.msgEl.textContent = msg;

      const e = this.engine;
      const parts = [
        { idle: '未初期化', loading: '準備中', worklet: 'Worklet', script: 'ScriptProc' }[e.mode] || e.mode,
      ];
      if (e.ctx) parts.push(Math.round(e.ctx.sampleRate / 100) / 10 + 'kHz', e.ctx.state);
      parts.push(e.srcType());
      parts.push(e.isAttached() ? '処理中' : '未接続');
      this.statusEl.textContent = parts.join(' · ') + ' · v' + VERSION;

      const pk = e.lastPeak;
      const level = pk == null ? '-' : pk > 0 ? Math.round(20 * Math.log10(pk)) + ' dB' : '無音';
      const st = e.procSemitones == null ? '-' : fmt(e.procSemitones);
      this.diagText.textContent = '診断: 入力レベル ' + level + ' / 処理側のキー ' + st;
      this.muteBtn.textContent = e.outputMuted ? '処理音を戻す' : '処理音を消す';
      this.muteBtn.classList.toggle('on', !!e.outputMuted);
    }
  }

  // ---------------------------------------------------------------------------
  // ページ監視
  // ---------------------------------------------------------------------------
  function currentVideoKey() {
    try {
      const u = new URL(location.href);
      const v = u.searchParams.get('v');
      if (v) return 'v:' + v;
      const m = u.pathname.match(/^\/(shorts|live|embed)\/([^/?#]+)/);
      if (m) return m[1] + ':' + m[2];
      return 'page:' + u.pathname;
    } catch (e) {
      return location.href;
    }
  }

  function findVideo() {
    const vids = Array.from(document.querySelectorAll('video'));
    if (vids.length === 0) return null;
    const playing = vids.find((v) => !v.paused && v.readyState > 2);
    if (playing) return playing;
    const main = document.querySelector('video.html5-main-video');
    if (main) return main;
    let best = null;
    let bestArea = -1;
    for (const v of vids) {
      const r = v.getBoundingClientRect();
      const a = r.width * r.height;
      if (a > bestArea) { best = v; bestArea = a; }
    }
    return best;
  }

  const engine = new AudioEngine();
  const ui = new PitchUI(engine);
  let lastKey = currentVideoKey();

  function tick() {
    ui.mount();
    const fs = document.fullscreenElement || document.webkitFullscreenElement;
    ui.host.style.display = fs ? 'none' : '';

    // 動画が切り替わったら ±0 に戻す
    const key = currentVideoKey();
    if (key !== lastKey) {
      lastKey = key;
      ui.setValue(0);
    }

    engine.setVideo(findVideo());
    if (!ui.panel.hidden) ui.render();
  }

  document.addEventListener('visibilitychange', () => {
    if (document.visibilityState === 'visible') engine.resume();
  });
  setInterval(tick, CONFIG.POLL_MS);
  tick();

  // デバッグ用（コンソールから参照可能）
  window.__ytPitchShifter = { engine, ui, CONFIG, PitchShifterDSP };
})();
