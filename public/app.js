'use strict';

/* ABX 盲听测试前端
 *
 * 播放引擎基于 Web Audio API：
 * - A / B 解码一次，X 按题解码并缓存
 * - 切换音源 / 切换题目时保持播放位置与暂停状态
 * - A / B / X 切换可做等功率交叉淡化（5～100 ms，可关闭）：新旧音源从
 *   同一时间位置并行播放，按 sin/cos 曲线完成增益交接；快速连续切换时
 *   从当前听感增益重新锚定，取消过时节点与回调，不叠加、不爆音、不漂移
 * - 统一时间轴 = min(A 时长, B 时长)
 * - 片段循环：入点 / 出点基于统一时间轴（区间 ≥ 0.5 秒），启用时用
 *   AudioBufferSourceNode 原生 loop 在出点处采样级跳回入点；切换音源 /
 *   换题 / 拖动进度后循环区间与播放 / 暂停状态保持，且不会越过较短音频
 * - 可选电平匹配：统一时间轴内汇总各声道样本计算 RMS，
 *   以较安静音源为基准仅衰减较响者（-24～0 dB），A / B / X 各经一个 GainNode
 */

const $ = (sel) => document.querySelector(sel);

// ---------------------------------------------------------------------------
// 全局状态
// ---------------------------------------------------------------------------

let session = null;          // { id, numTrials, recoveryToken }
let answers = [];            // 每题 'A' | 'B' | null
let confidences = [];        // 每题把握度：50/60/…/100 | null
let currentTrial = 0;

// ---------------------------------------------------------------------------
// 恢复标识（仅存本机浏览器 localStorage，不会离开本机）
// ---------------------------------------------------------------------------

const RECOVERY_KEY = 'abx.recovery';
let pendingResume = null;    // 页面加载时探测到的可恢复会话

// 创建会话时服务端下发的题序承诺值随恢复信息保存在本机；
// 恢复时用于对照服务端当前承诺（变化则拒绝继续答题），提交后用于结果页核验
function saveRecovery() {
  if (!session || !session.recoveryToken) return;
  localStorage.setItem(RECOVERY_KEY, JSON.stringify({
    token: session.recoveryToken,
    trial: currentTrial,
    commitment: session.commitment || null,
  }));
}

function loadSavedRecovery() {
  try {
    const saved = JSON.parse(localStorage.getItem(RECOVERY_KEY));
    if (saved && typeof saved.token === 'string') return saved;
  } catch (_) { /* 忽略损坏的本地数据 */ }
  return null;
}

function clearRecovery() {
  localStorage.removeItem(RECOVERY_KEY);
}

// ---------------------------------------------------------------------------
// 题序承诺核验（Web Crypto，纯前端计算）
//
// 固定格式与服务端一致：abx-v1|会话ID|题数|逐题A/B串|盐的十六进制
// 承诺值仅以创建会话时本机保存的原值为准；服务端提交后返回的承诺值只作展示，
// 绝不能拿来代替原承诺值。
// ---------------------------------------------------------------------------

const COMMITMENT_VERSION = 'abx-v1';

function commitmentMessage(id, numTrials, xSequence, saltHex) {
  return `${COMMITMENT_VERSION}|${id}|${numTrials}|${xSequence}|${saltHex}`;
}

/** 按固定格式计算承诺值（十六进制 SHA-256） */
async function computeCommitment(id, numTrials, xSequence, saltHex) {
  const buf = await crypto.subtle.digest(
    'SHA-256',
    new TextEncoder().encode(commitmentMessage(id, numTrials, xSequence, saltHex)),
  );
  return Array.from(new Uint8Array(buf))
    .map((b) => b.toString(16).padStart(2, '0'))
    .join('');
}

const HEX64_RE = /^[0-9a-f]{64}$/;
const SALT64_RE = /^[0-9a-f]{64}$/;

/**
 * 结果页核验：用创建时本机保存的原承诺值对照揭示数据重算。
 * 返回 { status: 'pass' | 'fail' | 'unknown', computed, detailConsistent }
 *  - unknown：本机没有原承诺值（无法核验），不使用服务端当前值代替
 *  - fail：原承诺值存在但重算不一致（题序 / 盐异常，或揭示数据自相矛盾）
 *  - pass：重算承诺与原值一致，且逐题映射串与结果明细逐题吻合
 */
async function verifyCommitment(results, originalCommitment) {
  const out = { status: 'unknown', computed: null, detailConsistent: null };
  if (!originalCommitment || typeof originalCommitment !== 'string') return out;
  if (
    !results ||
    typeof results.saltHex !== 'string' || !SALT64_RE.test(results.saltHex) ||
    typeof results.xSequence !== 'string' || !/^[AB]+$/.test(results.xSequence) ||
    !HEX64_RE.test(originalCommitment) ||
    !session
  ) {
    out.status = 'fail';
    return out;
  }
  const numTrials = session.numTrials;
  if (
    results.total !== numTrials ||
    results.xSequence.length !== numTrials ||
    !Array.isArray(results.detail) || results.detail.length !== numTrials
  ) {
    out.status = 'fail';
    return out;
  }
  // 映射串必须与结果明细逐题一致，防止只伪造哈希输入而明细不同
  const detailSequence = results.detail
    .slice()
    .sort((a, b) => a.trial - b.trial)
    .map((d) => d.x)
    .join('');
  out.detailConsistent = detailSequence === results.xSequence;

  out.computed = await computeCommitment(
    session.id, numTrials, results.xSequence, results.saltHex,
  );
  out.status = out.detailConsistent && out.computed === originalCommitment
    ? 'pass'
    : 'fail';
  return out;
}

let actx = null;             // AudioContext
const buffers = { A: null, B: null, X: null };
const xCache = new Map();    // trialIndex -> { buf, rms }
let timeline = 0;            // 统一时间轴（较短时长，秒）

let currentSrc = 'A';        // 当前音源 'A' | 'B' | 'X'
let playing = false;
const voices = [];           // 当前发声实例（交叉淡化期间新旧并行；最后一个为位置跟踪基准）
let startCtxTime = 0;        // 最新发声实例起点对应的 AudioContext 时间
let startOffset = 0;         // 最新发声实例起点对应的音频位置（秒）

// 交叉淡化：A / B / X 切换时新旧音源并行播放，按等功率曲线交接增益
const XFADE_MIN_MS = 5;      // 淡化时长下限（毫秒）
const XFADE_MAX_MS = 100;    // 淡化时长上限（毫秒）
let crossfadeOn = true;      // 开关状态
let crossfadeMs = 30;        // 淡化时长（毫秒，5～100）

// 电平匹配：A / B / X 各经一个 GainNode，仅衰减较响音源
const gains = { A: null, B: null, X: null };
const rms = { A: NaN, B: NaN, X: NaN };   // 统一时间轴内、汇总各声道的 RMS
const gainDb = { A: 0, B: 0, X: 0 };      // 各音源调整量（dB，≤ 0）
let levelRef = null;         // 基准 RMS（较安静音源）；A/B RMS 无效时为 null
let levelMatchOn = false;    // 开关状态

// 片段循环：入点 / 出点（秒，基于统一时间轴；null = 未设置）
const MIN_LOOP = 0.5;        // 循环区间最短时长（秒）
let loopIn = null;
let loopOut = null;

// ---------------------------------------------------------------------------
// 视图切换
// ---------------------------------------------------------------------------

function show(viewId) {
  document.querySelectorAll('.view').forEach((v) => v.classList.add('hidden'));
  $('#' + viewId).classList.remove('hidden');
}

// ---------------------------------------------------------------------------
// 播放引擎
// ---------------------------------------------------------------------------

function position() {
  if (!playing) return startOffset;
  const t = startOffset + actx.currentTime - startCtxTime;
  // 循环播放中：到达出点后从入点继续，显示位置在 [入点, 出点) 内回绕
  if (loopActive() && startOffset < loopOut && t >= loopOut) {
    return loopIn + ((t - loopIn) % (loopOut - loopIn));
  }
  return Math.min(t, timeline);
}

// 等功率交叉淡化曲线：淡入 sin、淡出 cos（0→π/2），交接中总功率保持恒定
const XFADE_STEPS = 64;      // 曲线采样点数
const xfadeCurves = new Map();   // 'in:30' / 'out:30' -> Float32Array（按时长缓存）

function xfadeCurve(kind, ms) {
  const key = kind + ':' + ms;
  let c = xfadeCurves.get(key);
  if (!c) {
    c = new Float32Array(XFADE_STEPS);
    for (let i = 0; i < XFADE_STEPS; i++) {
      const a = (i / (XFADE_STEPS - 1)) * (Math.PI / 2);
      c[i] = kind === 'in' ? Math.sin(a) : Math.cos(a);
    }
    xfadeCurves.set(key, c);
  }
  return c;
}

/** 淡化时长归一化：限制在 5～100 ms，非法值回退为默认 30 ms */
function clampXfadeMs(v) {
  const n = Math.round(Number(v));
  if (!Number.isFinite(n)) return 30;
  return Math.min(XFADE_MAX_MS, Math.max(XFADE_MIN_MS, n));
}

/** 回收发声实例：取消淡化定时器与 ended 回调，停止并断开节点 */
function removeVoice(v) {
  if (v.timer) { clearTimeout(v.timer); v.timer = null; }
  v.node.onended = null;
  try { v.node.stop(); } catch (_) { /* 已停止 */ }
  v.node.disconnect();
  v.fade.disconnect();
  const i = voices.indexOf(v);
  if (i >= 0) voices.splice(i, 1);
}

/** 立即停止全部发声实例（暂停 / 拖动 / 换题 / 循环变更时一致收束过渡） */
function stopAllVoices() {
  while (voices.length) removeVoice(voices[voices.length - 1]);
}

/**
 * 从指定位置创建发声实例：BufferSource → 淡化 GainNode → 电平匹配 GainNode。
 * 循环设置与电平匹配对新实例同样生效；fadeInMs > 0 时按等功率 sin 曲线淡入。
 * 返回实例；无可播内容（已到时间轴末尾且无循环）时返回 null。
 */
function startVoice(src, offset, fadeInMs) {
  const buf = buffers[src];
  // 循环启用且起点在出点之前：用原生 loop，到达出点（loopEnd）即采样级
  // 精确跳回入点（loopStart）；loopIn/loopOut ≤ timeline ≤ 各音源时长，
  // 因此不会越过较短音频的有效时长
  const useLoop = loopActive() && offset < loopOut;
  const remain = Math.max(0, Math.min(timeline, buf.duration) - offset);
  if (!useLoop && remain <= 0) return null;

  const node = actx.createBufferSource();
  node.buffer = buf;
  const fade = actx.createGain();   // 交叉淡化包络（电平匹配增益在 gains[src] 上）
  node.connect(fade);
  fade.connect(gains[src]);         // 经各音源的 GainNode 输出（电平匹配）
  const v = { src, node, fade, timer: null };

  if (useLoop) {
    node.loop = true;
    node.loopStart = loopIn;
    node.loopEnd = loopOut;
    node.start(0, offset);
  } else {
    node.onended = () => {
      // 自然播放到时间轴末尾；仅当本实例仍是当前（最新）实例时收束播放状态
      const isCurrent = voices[voices.length - 1] === v;
      removeVoice(v);
      if (isCurrent) {
        playing = false;
        startOffset = 0;
        updatePlayBtn();
      }
    };
    node.start(0, offset, remain);
  }

  const now = actx.currentTime;
  if (fadeInMs > 0) {
    fade.gain.setValueAtTime(0, now);
    fade.gain.setValueCurveAtTime(xfadeCurve('in', fadeInMs), now, fadeInMs / 1000);
  } else {
    fade.gain.value = 1;
  }

  voices.push(v);
  // 位置跟踪锚点切换到最新实例（显示位置以它为准，避免进度漂移）
  startCtxTime = now;
  startOffset = offset;
  return v;
}

/**
 * 让发声实例从当前听感增益按等功率 cos 曲线淡出，结束后回收。
 * 快速连续切换时，进行中的淡化被取消（定时器与增益事件）并重新锚定，
 * 始终从当前实际增益继续淡出，不会音量叠加或爆音。
 */
function fadeOutVoice(v, fadeMs) {
  if (v.timer) { clearTimeout(v.timer); v.timer = null; }
  const now = actx.currentTime;
  const g = v.fade.gain.value;      // 当前听感增益（含进行中淡化的进度）
  const p = v.fade.gain;
  p.cancelScheduledValues(now);
  const base = xfadeCurve('out', fadeMs);
  p.setValueCurveAtTime(g === 1 ? base : base.map((x) => x * g), now, fadeMs / 1000);
  v.timer = setTimeout(() => removeVoice(v), fadeMs + 80);
}

function play() {
  if (playing || !buffers[currentSrc]) return;
  if (startOffset >= timeline) startOffset = 0;
  if (!startVoice(currentSrc, startOffset, 0)) return;
  playing = true;
  updatePlayBtn();
}

function pause() {
  if (!playing) return;
  startOffset = position();
  stopAllVoices();
  playing = false;
  updatePlayBtn();
}

/**
 * 切换 A / B / X，保持播放位置与暂停状态。
 * 播放中且淡化开启时做等功率交叉淡化：全部旧实例从各自当前听感增益淡出
 * 并定时回收，新实例从同一时间位置淡入，循环区间与电平匹配对新旧实例
 * 同时生效；快速连续点击始终从当前听感平滑转向最后一次选择。
 */
function switchSource(which) {
  if (which === currentSrc || !buffers[which]) return;
  let pos = position();
  if (pos >= timeline) pos = 0;
  const wasPlaying = playing;
  const fadeMs = wasPlaying && crossfadeOn ? crossfadeMs : 0;
  currentSrc = which;

  if (fadeMs > 0 && voices.length) {
    for (const v of voices) fadeOutVoice(v, fadeMs);  // 旧实例全部淡出
    if (!startVoice(which, pos, fadeMs)) {            // 新实例同位置淡入
      // 理论上不可达（pos 已钳制在时间轴内）；防御性收束
      playing = false;
      startOffset = 0;
      updatePlayBtn();
    }
  } else {
    stopAllVoices();
    playing = false;
    startOffset = pos;
    if (wasPlaying) play();
  }
  updateSrcButtons();
}

function seekTo(t) {
  const wasPlaying = playing;
  stopAllVoices();
  playing = false;
  startOffset = Math.max(0, Math.min(t, timeline));
  if (wasPlaying) play();
  updateTransport();
}

// ---------------------------------------------------------------------------
// 片段循环：在统一时间轴上设置入点 / 出点，播放到出点即从入点继续
// ---------------------------------------------------------------------------

/** 循环是否生效（入 / 出点均已设置且区间 ≥ 0.5 秒） */
function loopActive() {
  return loopIn !== null && loopOut !== null && loopOut - loopIn >= MIN_LOOP;
}

/** 归一化入 / 出点：限制在 [0, timeline] 内，且区间至少 0.5 秒（必要时回移入点） */
function normalizeLoop() {
  if (loopIn !== null) loopIn = Math.max(0, Math.min(loopIn, timeline));
  if (loopOut !== null) loopOut = Math.max(0, Math.min(loopOut, timeline));
  if (loopIn !== null && loopOut !== null && loopOut - loopIn < MIN_LOOP) {
    loopOut = Math.min(timeline, loopIn + MIN_LOOP);
    loopIn = Math.max(0, loopOut - MIN_LOOP);
  }
}

/**
 * 循环区间变更后无缝重建播放（保持播放 / 暂停状态）：
 * 当前位置已越过新出点时立即跳回入点；循环未参与播放时不打断当前声音
 */
function restartForLoop(pos, wasActive) {
  const snap = loopActive() && pos >= loopOut;
  if (playing) {
    if (!wasActive && !loopActive()) return;
    stopAllVoices();
    playing = false;
    startOffset = snap ? loopIn : pos;
    play();
  } else if (snap) {
    startOffset = loopIn;
    updateTransport();
  }
}

/** 渲染循环状态：按钮高亮、状态行、时间轴上的范围高亮与入 / 出点刻度 */
function renderLoop() {
  const inSet = loopIn !== null;
  const outSet = loopOut !== null;
  const active = loopActive();

  $('#btnLoopIn').classList.toggle('set', inSet);
  $('#btnLoopOut').classList.toggle('set', outSet);
  $('#btnLoopClear').disabled = !inSet && !outSet;

  const info = $('#loopInfo');
  if (timeline > 0 && timeline < MIN_LOOP) {
    info.textContent = '音频不足 0.5 秒，无法设置循环';
  } else if (active) {
    info.textContent =
      `循环已启用：${fmt(loopIn)} → ${fmt(loopOut)}（${(loopOut - loopIn).toFixed(1)} 秒）`;
  } else if (inSet && outSet) {
    info.textContent = '循环区间过短（至少 0.5 秒）';
  } else if (inSet) {
    info.textContent = `入点 ${fmt(loopIn)} · 待设置出点`;
  } else if (outSet) {
    info.textContent = `出点 ${fmt(loopOut)} · 待设置入点`;
  } else {
    info.textContent = '循环未设置';
  }
  info.classList.toggle('on', active);

  // 时间轴下方的循环范围高亮与入 / 出点刻度
  const region = $('#loopRegion');
  const showRegion = active && timeline > 0;
  region.classList.toggle('show', showRegion);
  if (showRegion) {
    region.style.left = `${(loopIn / timeline) * 100}%`;
    region.style.width = `${((loopOut - loopIn) / timeline) * 100}%`;
  }
  const edgeIn = $('#loopEdgeIn');
  const edgeOut = $('#loopEdgeOut');
  edgeIn.classList.toggle('show', inSet && timeline > 0);
  edgeOut.classList.toggle('show', outSet && timeline > 0);
  if (inSet && timeline > 0) edgeIn.style.left = `${(loopIn / timeline) * 100}%`;
  if (outSet && timeline > 0) edgeOut.style.left = `${(loopOut / timeline) * 100}%`;
}

// ---------------------------------------------------------------------------
// 电平匹配（可选）：消除 A/B 响度差造成的盲测线索
// ---------------------------------------------------------------------------

const RMS_MIN = 1e-6;        // RMS 下限，低于此值视为无声
const GAIN_MIN_DB = -24;     // 衰减下限（dB）

/** 统一时间轴内、汇总各声道样本的 RMS */
function computeRms(buf, seconds) {
  const len = Math.min(buf.length, Math.floor(seconds * buf.sampleRate));
  if (len <= 0) return NaN;
  let sum = 0;
  for (let ch = 0; ch < buf.numberOfChannels; ch++) {
    const data = buf.getChannelData(ch);
    for (let i = 0; i < len; i++) sum += data[i] * data[i];
  }
  return Math.sqrt(sum / (len * buf.numberOfChannels));
}

const validRms = (r) => Number.isFinite(r) && r >= RMS_MIN;

/** 由 RMS 重算各音源调整量（dB）：以较安静音源为基准，仅衰减较响者 */
function refreshLevelMatch() {
  // A 或 B 的 RMS 无效（< 1e-6 或非有限值）时不做匹配，全部保持 0 dB
  levelRef = validRms(rms.A) && validRms(rms.B) ? Math.min(rms.A, rms.B) : null;
  for (const k of ['A', 'B', 'X']) {
    let db = 0;
    if (levelRef !== null && validRms(rms[k])) {
      db = 20 * Math.log10(levelRef / rms[k]);
      db = Math.max(GAIN_MIN_DB, Math.min(0, db)); // 衰减限制在 -24～0 dB
    }
    gainDb[k] = db;
  }
  applyGains();
  renderLevelInfo();
}

/** 按开关状态把调整量写入 GainNode；不打断播放，关闭立即恢复原始电平 */
function applyGains() {
  if (!actx) return;
  for (const k of ['A', 'B', 'X']) {
    if (gains[k]) {
      gains[k].gain.value = Math.pow(10, (levelMatchOn ? gainDb[k] : 0) / 20);
    }
  }
}

function renderLevelInfo() {
  const fmtDb = (db) => {
    const s = db.toFixed(1);
    return s === '-0.0' ? '0.0' : s;
  };
  const el = $('#levelInfo');
  el.textContent = `A ${fmtDb(gainDb.A)} dB · B ${fmtDb(gainDb.B)} dB`;
  el.classList.toggle('off', !levelMatchOn);
}

// ---------------------------------------------------------------------------
// 音频加载
// ---------------------------------------------------------------------------

async function fetchBuffer(url) {
  const res = await fetch(url);
  if (!res.ok) throw new Error('音频加载失败');
  const raw = await res.arrayBuffer();
  return actx.decodeAudioData(raw);
}

async function loadTrial(n) {
  currentTrial = n;
  saveRecovery(); // 记住当前题号，刷新后可回到本题
  if (!xCache.has(n)) {
    const buf = await fetchBuffer(`/api/session/${session.id}/trial/${n}/x`);
    // 每题 X 与 A/B 按同一规则计算 RMS（统一时间轴内、汇总各声道）
    xCache.set(n, { buf, rms: computeRms(buf, timeline) });
  }
  const cached = xCache.get(n);
  buffers.X = cached.buf;
  rms.X = cached.rms;
  refreshLevelMatch(); // X 的调整量随题更新
  // 若当前正在听 X，无缝换成本题的 X（保持位置与播放状态）
  if (currentSrc === 'X') {
    const pos = position();
    const wasPlaying = playing;
    stopAllVoices();
    playing = false;
    startOffset = pos;
    if (wasPlaying) play();
  }
  renderTrial();
}

// ---------------------------------------------------------------------------
// UI 渲染
// ---------------------------------------------------------------------------

function fmt(t) {
  const m = Math.floor(t / 60);
  const s = t - m * 60;
  return `${m}:${s.toFixed(1).padStart(4, '0')}`;
}

function updatePlayBtn() {
  $('#btnPlay').textContent = playing ? '⏸ 暂停' : '▶ 播放';
}

function updateTransport() {
  $('#seek').value = position();
  $('#timeLabel').textContent = `${fmt(position())} / ${fmt(timeline)}`;
}

function updateSrcButtons() {
  document.querySelectorAll('.src-btn').forEach((b) => {
    b.classList.toggle('active', b.dataset.src === currentSrc);
  });
}

function renderTrial() {
  $('#trialLabel').textContent = `第 ${currentTrial + 1} / ${session.numTrials} 题`;
  $('#btnPrev').disabled = currentTrial === 0;
  $('#btnNext').disabled = currentTrial === session.numTrials - 1;

  const ans = answers[currentTrial];
  $('#btnAnsA').classList.toggle('selected', ans === 'A');
  $('#btnAnsB').classList.toggle('selected', ans === 'B');
  document.querySelectorAll('.conf-btn').forEach((b) => {
    b.classList.toggle('selected', confidences[currentTrial] === Number(b.dataset.conf));
  });

  // 进度圆点：答案与把握度齐全才算完成，只有一项为半完成
  const progress = $('#progress');
  progress.innerHTML = '';
  for (let i = 0; i < session.numTrials; i++) {
    const dot = document.createElement('button');
    dot.className = 'dot';
    const done = Boolean(answers[i]) && confidences[i] != null;
    const partial = Boolean(answers[i]) !== (confidences[i] != null);
    if (done) dot.classList.add('done');
    else if (partial) dot.classList.add('partial');
    if (i === currentTrial) dot.classList.add('current');
    dot.textContent = i + 1;
    dot.addEventListener('click', () => loadTrial(i));
    progress.appendChild(dot);
  }

  const incomplete = answers.filter((a, i) => !a || confidences[i] == null).length;
  $('#btnSubmit').disabled = incomplete > 0;
  $('#btnSubmit').textContent = incomplete === 0
    ? '提交并揭晓答案'
    : `提交并揭晓答案（还有 ${incomplete} 题未完成）`;
}

function tick() {
  if (playing) updateTransport();
  requestAnimationFrame(tick);
}

// ---------------------------------------------------------------------------
// 事件绑定
// ---------------------------------------------------------------------------

/** 进入测试视图：解码 A/B、初始化播放状态并加载当前题（新建与恢复共用） */
async function enterTest() {
  // AudioContext 需在用户手势中创建
  actx = actx || new (window.AudioContext || window.webkitAudioContext)();
  await actx.resume();

  // 每个音源一个 GainNode（电平匹配用），只创建一次
  if (!gains.A) {
    for (const k of ['A', 'B', 'X']) {
      gains[k] = actx.createGain();
      gains[k].connect(actx.destination);
    }
  }

  buffers.A = await fetchBuffer(`/api/session/${session.id}/audio/A`);
  buffers.B = await fetchBuffer(`/api/session/${session.id}/audio/B`);
  // 统一时间轴：以较短时长为准
  timeline = Math.min(buffers.A.duration, buffers.B.duration);
  $('#seek').max = timeline;

  // 片段循环：新会话清空；音频短于 0.5 秒时禁用循环按钮
  loopIn = null;
  loopOut = null;
  const canLoop = timeline >= MIN_LOOP;
  $('#btnLoopIn').disabled = !canLoop;
  $('#btnLoopOut').disabled = !canLoop;
  renderLoop();

  // 电平匹配：解码后在统一时间轴内汇总各声道样本计算 RMS
  rms.A = computeRms(buffers.A, timeline);
  rms.B = computeRms(buffers.B, timeline);
  rms.X = NaN; // 待 loadTrial 解码本题 X 后计算
  levelMatchOn = $('#chkLevelMatch').checked;
  refreshLevelMatch();

  // 交叉淡化：读取界面设置（时长非法时回退为默认 30 ms）
  crossfadeOn = $('#chkCrossfade').checked;
  crossfadeMs = clampXfadeMs($('#crossfadeMs').value);
  $('#crossfadeMs').value = crossfadeMs;
  $('#crossfadeMs').disabled = !crossfadeOn;

  stopAllVoices(); // 收束可能残留的发声实例与淡化定时器
  currentSrc = 'A';
  playing = false;
  startOffset = 0;
  updateSrcButtons();
  updatePlayBtn();
  updateTransport();

  await loadTrial(currentTrial);
  show('view-test');
}

$('#btnStart').addEventListener('click', async () => {
  const errEl = $('#uploadError');
  errEl.textContent = '';
  const fa = $('#fileA').files[0];
  const fb = $('#fileB').files[0];
  if (!fa || !fb) {
    errEl.textContent = '请同时选择音频 A 和音频 B';
    return;
  }

  const btn = $('#btnStart');
  btn.disabled = true;
  btn.textContent = '上传并解码中…';
  try {
    // 开始新测试即放弃旧的待恢复会话（主动删除，恢复标识随之失效）
    if (pendingResume) {
      await fetch(`/api/session/${pendingResume.id}`, { method: 'DELETE' }).catch(() => {});
      pendingResume = null;
      const oldCard = $('#view-resume');
      oldCard.classList.add('hidden');
      oldCard.classList.remove('tampered');
      $('#resumeCommitError').textContent = '';
      $('#btnResume').classList.remove('hidden');
    }

    const fd = new FormData();
    fd.append('a', fa);
    fd.append('b', fb);
    fd.append('numTrials', $('#numTrials').value);
    const res = await fetch('/api/session', { method: 'POST', body: fd });
    const data = await res.json();
    if (!res.ok) throw new Error(data.error || '创建会话失败');

    session = data;
    answers = Array(data.numTrials).fill(null);
    confidences = Array(data.numTrials).fill(null);
    currentTrial = 0;
    xCache.clear();
    saveRecovery(); // 保存恢复标识，刷新/重开页面可找回本会话

    await enterTest();
  } catch (e) {
    errEl.textContent = e.message;
  } finally {
    btn.disabled = false;
    btn.textContent = '开始测试';
  }
});

// ---------------------------------------------------------------------------
// 会话恢复（刷新 / 重新打开页面后找回未提交的测试）
// ---------------------------------------------------------------------------

async function initRecovery() {
  const saved = loadSavedRecovery();
  if (!saved) return;
  try {
    const res = await fetch('/api/session/recover', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ token: saved.token }),
    });
    if (!res.ok) throw new Error('recover failed');
    const data = await res.json();
    // 题序承诺核验：服务端当前承诺必须与创建时本机保存的原值一致，
    // 任何变化都视为题序可能被中途篡改，阻止继续答题（只能删除该会话）
    const tampered = typeof saved.commitment === 'string'
      && data.commitment !== saved.commitment;
    pendingResume = {
      ...data,
      token: saved.token,
      trial: Math.min(Math.max(0, saved.trial | 0), data.numTrials - 1),
      tampered: Boolean(tampered),
    };
    const card = $('#view-resume');
    card.classList.toggle('tampered', tampered);
    if (tampered) {
      $('#resumeInfo').textContent =
        `检测到会话异常：该会话（共 ${data.numTrials} 题）的题序承诺值已与创建时本机保存的不一致，` +
        '题序可能在提交前被篡改。为保证测试有效，已阻止继续答题。';
      $('#resumeCommitError').textContent =
        '⛔ 题序承诺核验未通过：请勿继续使用该会话，可选择删除它。';
      $('#btnResume').classList.add('hidden');
    } else {
      $('#resumeCommitError').textContent = '';
      $('#btnResume').classList.remove('hidden');
      const answered = data.answers.filter(
        (a, i) => a && data.confidences[i] != null,
      ).length;
      $('#resumeInfo').textContent =
        `检测到本机有未提交的测试：共 ${data.numTrials} 题，已完成 ${answered} 题，` +
        `上次进行到第 ${pendingResume.trial + 1} 题。`;
    }
    card.classList.remove('hidden');
  } catch (_) {
    clearRecovery(); // 会话已提交、删除或过期，恢复标识不再有效
  }
}

$('#btnResume').addEventListener('click', async () => {
  if (!pendingResume || pendingResume.tampered) return; // 承诺不一致：禁止继续
  const btn = $('#btnResume');
  btn.disabled = true;
  btn.textContent = '正在恢复…';
  const resume = pendingResume;
  try {
    session = {
      id: resume.id,
      numTrials: resume.numTrials,
      recoveryToken: resume.token,
      // 必须保留创建时的原承诺值：loadTrial 会再次 saveRecovery，
      // 缺失会导致本机原承诺被 null 覆盖，提交后无法核验
      commitment: resume.commitment,
    };
    answers = resume.answers.slice();
    confidences = resume.confidences.slice();
    currentTrial = resume.trial;
    xCache.clear();
    await enterTest();
    pendingResume = null;
    $('#view-resume').classList.add('hidden');
  } catch (e) {
    alert(e.message || '恢复失败');
    btn.disabled = false;
    btn.textContent = '继续上次测试';
  }
});

$('#btnDiscardResume').addEventListener('click', async () => {
  if (pendingResume) {
    await fetch(`/api/session/${pendingResume.id}`, { method: 'DELETE' }).catch(() => {});
  }
  pendingResume = null;
  clearRecovery();
  const card = $('#view-resume');
  card.classList.add('hidden');
  card.classList.remove('tampered');
  $('#resumeCommitError').textContent = '';
  $('#btnResume').classList.remove('hidden');
});

$('#btnPlay').addEventListener('click', async () => {
  await actx.resume();
  if (playing) pause();
  else play();
});

document.querySelectorAll('.src-btn').forEach((b) => {
  b.addEventListener('click', () => switchSource(b.dataset.src));
});

$('#seek').addEventListener('input', (e) => seekTo(parseFloat(e.target.value)));

// 片段循环：以当前播放位置设置入点 / 出点（先后次序不限），一键清除。
// 循环区间是全局状态：切换 A / B / X、换题、拖动进度都不会改变它
$('#btnLoopIn').addEventListener('click', () => {
  if (timeline < MIN_LOOP) return;
  const wasActive = loopActive();
  const pos = position();
  loopIn = pos;
  normalizeLoop();
  restartForLoop(pos, wasActive);
  renderLoop();
});

$('#btnLoopOut').addEventListener('click', () => {
  if (timeline < MIN_LOOP) return;
  const wasActive = loopActive();
  const pos = position();
  loopOut = pos;
  normalizeLoop();
  restartForLoop(pos, wasActive);
  renderLoop();
});

$('#btnLoopClear').addEventListener('click', () => {
  const wasActive = loopActive();
  const pos = position(); // 先取当前实际位置（旧循环配置下的回绕位置）
  loopIn = loopOut = null;
  if (playing && wasActive) {
    stopAllVoices();
    playing = false;
    startOffset = pos;
    play();
  }
  renderLoop();
});

// 电平匹配开关：只改 GainNode 增益，播放位置与播放/暂停状态不受影响
$('#chkLevelMatch').addEventListener('change', (e) => {
  levelMatchOn = e.target.checked;
  applyGains(); // 关闭后立即恢复原始电平
  renderLevelInfo();
});

// 交叉淡化设置：时长 5～100 ms，可整体关闭；只影响之后的切换，
// 进行中的淡化会自然走完（≤ 100 ms），不产生爆音
$('#chkCrossfade').addEventListener('change', (e) => {
  crossfadeOn = e.target.checked;
  $('#crossfadeMs').disabled = !crossfadeOn;
});

$('#crossfadeMs').addEventListener('change', (e) => {
  crossfadeMs = clampXfadeMs(e.target.value);
  e.target.value = crossfadeMs;
});

$('#btnPrev').addEventListener('click', () => { if (currentTrial > 0) loadTrial(currentTrial - 1); });
$('#btnNext').addEventListener('click', () => { if (currentTrial < session.numTrials - 1) loadTrial(currentTrial + 1); });

// 答案与把握度一起保存到服务端：任一项变更即把本题当前已选内容一并提交
async function saveTrial() {
  renderTrial();
  const payload = { trial: currentTrial };
  if (answers[currentTrial]) payload.answer = answers[currentTrial];
  if (confidences[currentTrial] != null) payload.confidence = confidences[currentTrial];
  const res = await fetch(`/api/session/${session.id}/answer`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(payload),
  });
  if (!res.ok) {
    const data = await res.json().catch(() => ({}));
    alert(data.error || '答案保存失败');
  }
}

$('#btnAnsA').addEventListener('click', () => {
  answers[currentTrial] = 'A';
  saveTrial();
});
$('#btnAnsB').addEventListener('click', () => {
  answers[currentTrial] = 'B';
  saveTrial();
});
document.querySelectorAll('.conf-btn').forEach((b) => {
  b.addEventListener('click', () => {
    confidences[currentTrial] = Number(b.dataset.conf);
    saveTrial();
  });
});

$('#btnSubmit').addEventListener('click', async () => {
  if (!confirm('提交后将一次性揭晓全部答案，且不可再修改。确定提交？')) return;
  // 先取出创建时本机保存的原承诺值（核验唯一基准），再清掉恢复信息；
  // 绝不能用服务端当前返回的承诺值代替
  const originalCommitment = (loadSavedRecovery() || {}).commitment || null;
  const res = await fetch(`/api/session/${session.id}/submit`, { method: 'POST' });
  const data = await res.json();
  if (!res.ok) {
    alert(data.error || '提交失败');
    return;
  }
  pause();
  clearRecovery(); // 提交后恢复标识立即失效（服务端同步作废）
  await showResults(data.results, originalCommitment);
});

$('#btnAgain').addEventListener('click', async () => {
  pause();
  if (session) {
    await fetch(`/api/session/${session.id}`, { method: 'DELETE' }).catch(() => {});
  }
  session = null;
  answers = [];
  confidences = [];
  xCache.clear();
  clearRecovery();
  buffers.A = buffers.B = buffers.X = null;
  rms.A = rms.B = rms.X = NaN;
  refreshLevelMatch(); // 清空调整量显示，增益归零
  currentSrc = 'A';
  startOffset = 0;
  loopIn = null;
  loopOut = null;
  $('#fileA').value = '';
  $('#fileB').value = '';
  show('view-upload');
});

// ---------------------------------------------------------------------------
// 结果展示
// ---------------------------------------------------------------------------

async function showResults(results, originalCommitment) {
  const pct = (results.accuracy * 100).toFixed(1);
  $('#scoreLabel').textContent =
    `答对 ${results.correct} / ${results.total} 题，正确率 ${pct}%`;

  const tbody = $('#resultTable tbody');
  tbody.innerHTML = '';
  for (const d of results.detail) {
    const tr = document.createElement('tr');
    tr.className = d.correct ? 'right' : 'wrong';
    tr.innerHTML =
      `<td>${d.trial}</td><td>${d.x}</td><td>${d.answer}</td>` +
      `<td>${d.confidence}%</td>` +
      `<td>${d.correct ? '✓ 正确' : '✗ 错误'}</td>`;
    tbody.appendChild(tr);
  }
  renderCalibration(results.calibration);
  await renderCommitmentVerify(results, originalCommitment);
  show('view-result');
}

/**
 * 结果页题序承诺核验：用创建时本机保存的承诺值（唯一基准）与提交后揭示的
 * 盐 + 逐题 A/B 串按固定格式用 Web Crypto 重算，显示
 * 「核验通过 / 核验失败 / 无法核验」。服务端返回的承诺值仅作展示对照，
 * 不能代替本机原值。
 */
async function renderCommitmentVerify(results, originalCommitment) {
  const box = $('#commitVerify');
  const verdictEl = $('#commitVerdict');
  const descEl = $('#commitDesc');
  box.classList.remove('pass', 'fail', 'unknown');

  let v;
  try {
    v = await verifyCommitment(results, originalCommitment);
  } catch (_) {
    v = { status: 'fail', computed: null, detailConsistent: null };
  }

  const serverCommitment = results && typeof results.commitment === 'string'
    ? results.commitment : '';
  const row = (k, val) =>
    `<tr><th>${k}</th><td class="mono">${val || '（缺失）'}</td></tr>`;
  const detailRows = [
    row('创建时本机保存的承诺值', originalCommitment),
  ];
  if (serverCommitment) detailRows.push(row('服务端揭示的承诺值', serverCommitment));
  if (v.computed) detailRows.push(row('本机重新计算的承诺值', v.computed));
  if (results && results.saltHex) detailRows.push(row('揭示的随机盐（hex）', results.saltHex));
  if (results && results.xSequence) detailRows.push(row('逐题 A/B 串', results.xSequence));
  $('#commitDetails tbody').innerHTML = detailRows.join('');

  if (v.status === 'pass') {
    box.classList.add('pass');
    verdictEl.textContent = '✓ 核验通过';
    descEl.textContent =
      '用提交后揭示的随机盐与逐题 A/B 串，按固定格式 ' +
      'abx-v1|会话ID|题数|逐题A/B串|盐hex 在本机重算 SHA-256，' +
      '结果与创建会话时保存在本机的承诺值完全一致，且与逐题明细吻合：' +
      '题序在整个测试过程中未被篡改。';
  } else if (v.status === 'fail') {
    box.classList.add('fail');
    verdictEl.textContent = '✗ 核验失败';
    descEl.textContent =
      '用揭示的盐与逐题 A/B 串重算的承诺值（或结果明细）与创建时本机保存的承诺值不一致，' +
      '题序可能在提交前被篡改，或揭示数据不完整 / 自相矛盾。请不要采信本次结果。';
  } else {
    box.classList.add('unknown');
    verdictEl.textContent = '？ 无法核验';
    descEl.textContent =
      '本机没有创建会话时保存的原承诺值（例如更换了浏览器、清理过站点数据，' +
      '或本机存储被禁用），缺少核验基准，因此无法判断题序是否被中途修改。' +
      '服务端当前返回的承诺值不能代替原承诺值作为基准。';
  }
}

// ---------------------------------------------------------------------------
// 把握度校准：同一 0～100% 横轴上绘制把握度标记、正确率点与 95% 精确区间
// ---------------------------------------------------------------------------

function renderCalibration(calibration) {
  const chart = $('#calibChart');
  chart.innerHTML = '';
  const tbody = $('#calibTable tbody');
  tbody.innerHTML = '';

  for (const row of calibration) {
    // ---- 图：每档一行，横轴统一为 0～100% ----
    const rowEl = document.createElement('div');
    rowEl.className = 'calib-row';
    const label = document.createElement('span');
    label.className = 'calib-label';
    label.textContent = `${row.confidence}%`;
    const track = document.createElement('div');
    track.className = 'calib-track';

    if (row.n === 0) {
      track.classList.add('empty');
      const empty = document.createElement('span');
      empty.className = 'calib-empty';
      empty.textContent = '无数据';
      track.appendChild(empty);
    } else {
      const [lo, hi] = row.ci;
      const ci = document.createElement('div');
      ci.className = 'calib-ci';
      ci.style.left = `${lo * 100}%`;
      ci.style.width = `${(hi - lo) * 100}%`;
      ci.title = `95% 精确置信区间 [${(lo * 100).toFixed(1)}%, ${(hi * 100).toFixed(1)}%]`;

      const acc = document.createElement('div');
      acc.className = 'calib-acc';
      acc.style.left = `${row.accuracy * 100}%`;
      acc.title = `实际正确率 ${(row.accuracy * 100).toFixed(1)}%（${row.k}/${row.n}）`;

      const conf = document.createElement('div');
      // 把握度未落入区间 → 突出显示（标红）
      conf.className = row.covered ? 'calib-conf' : 'calib-conf off';
      conf.style.left = `${row.confidence}%`;
      conf.title = row.covered
        ? `自评把握度 ${row.confidence}%，落入区间`
        : `自评把握度 ${row.confidence}%，未落入区间（${row.confidence / 100 > hi ? '过度自信' : '信心不足'}）`;

      track.append(ci, acc, conf);
    }
    rowEl.append(label, track);
    chart.appendChild(rowEl);

    // ---- 表：分档数值 ----
    const tr = document.createElement('tr');
    if (row.n === 0) {
      tr.innerHTML = `<td>${row.confidence}%</td><td>0</td><td colspan="3">无数据</td>`;
    } else {
      if (!row.covered) tr.className = 'miscal';
      const [lo, hi] = row.ci;
      tr.innerHTML =
        `<td>${row.confidence}%</td><td>${row.n}</td><td>${row.k}</td>` +
        `<td>${(row.accuracy * 100).toFixed(1)}%</td>` +
        `<td>[${(lo * 100).toFixed(1)}%, ${(hi * 100).toFixed(1)}%]</td>`;
    }
    tbody.appendChild(tr);
  }

  // 共用横轴：刻度每 10%，标签每 20%
  const axisRow = document.createElement('div');
  axisRow.className = 'calib-row';
  const spacer = document.createElement('span');
  spacer.className = 'calib-label';
  const axis = document.createElement('div');
  axis.className = 'calib-axis';
  for (let v = 0; v <= 100; v += 10) {
    const tick = document.createElement('div');
    tick.className = 'calib-tick';
    tick.style.left = `${v}%`;
    axis.appendChild(tick);
    if (v % 20 === 0) {
      const lab = document.createElement('span');
      lab.className = 'calib-tick-label';
      lab.style.left = `${v}%`;
      lab.textContent = `${v}%`;
      if (v === 0) lab.style.transform = 'none';
      else if (v === 100) lab.style.transform = 'translateX(-100%)';
      axis.appendChild(lab);
    }
  }
  axisRow.append(spacer, axis);
  chart.appendChild(axisRow);
}

// 启动 UI 刷新循环，并探测本机是否有可恢复的未提交会话
tick();
initRecovery();
