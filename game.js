'use strict';

const COLS = 10;
const ROWS = 20;
const BLOCK = 30;
const MAX_ENERGY = 100;

const COLORS = [
  null,
  '#4dd0e1', // 1 I
  '#ffd54f', // 2 O
  '#ba68c8', // 3 T
  '#81c784', // 4 S
  '#e57373', // 5 Z
  '#7986cb', // 6 J
  '#ffb74d', // 7 L
  '#f48fb1', // 8 + cross
  '#80cbc4', // 9 U
  '#ce93d8', // 10 Y
  '#fff176', // 11 1×1
  '#ff8a65', // 12 hollow 3×3
  null,      // 13 power-up (rendered as rainbow)
];

const PIECES = [
  null,
  [[0,0,0,0],[1,1,1,1],[0,0,0,0],[0,0,0,0]], // 1 I
  [[2,2],[2,2]],                               // 2 O
  [[0,3,0],[3,3,3],[0,0,0]],                  // 3 T
  [[0,4,4],[4,4,0],[0,0,0]],                  // 4 S
  [[5,5,0],[0,5,5],[0,0,0]],                  // 5 Z
  [[6,0,0],[6,6,6],[0,0,0]],                  // 6 J
  [[0,0,7],[7,7,7],[0,0,0]],                  // 7 L
  [[0,8,0],[8,8,8],[0,8,0]],                  // 8 + cross
  [[9,0,9],[9,9,9],[0,0,0]],                  // 9 U
  [[0,10],[10,10],[0,10],[0,10]],             // 10 Y
  [[11]],                                      // 11 1×1
  [[12,12,12],[12,0,12],[12,12,12]],           // 12 hollow 3×3
];

const LINE_SCORES = [0, 100, 300, 500, 800];

// DOM refs
const canvas     = document.getElementById('board');
const ctx        = canvas.getContext('2d');
const nextCanvas = document.getElementById('next-canvas');
const nextCtx    = nextCanvas.getContext('2d');
const holdCanvas = document.getElementById('hold-canvas');
const holdCtx    = holdCanvas.getContext('2d');
const scoreEl    = document.getElementById('score');
const linesEl    = document.getElementById('lines');
const levelEl    = document.getElementById('level');
const overlay    = document.getElementById('overlay');
const overlayTitle = document.getElementById('overlay-title');
const overlayScore = document.getElementById('overlay-score');
const restartBtn = document.getElementById('restart-btn');

// ─── High Scores ──────────────────────────────────────────────────────────────

function loadScores() {
  try { return JSON.parse(localStorage.getItem('tetris_scores')) || []; }
  catch { return []; }
}

function saveScores(scores) {
  localStorage.setItem('tetris_scores', JSON.stringify(scores));
}

function isTopScore(s) {
  const scores = loadScores();
  return scores.length < 5 || s > scores[scores.length - 1].score;
}

function addScore(entry) {
  const scores = loadScores();
  scores.push(entry);
  scores.sort((a, b) => b.score - a.score);
  scores.splice(5);
  saveScores(scores);
  return scores.findIndex(s => s.ts === entry.ts);
}

function escapeHtml(str) {
  return String(str)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;')
    .replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

function renderScoreTable(containerId, highlightIndex) {
  const scores = loadScores();
  const el = document.getElementById(containerId);
  if (!el) return;
  if (scores.length === 0) {
    el.innerHTML = '<p class="hs-empty">No records yet</p>';
    return;
  }
  el.innerHTML = scores.map((s, i) => `
    <div class="hs-row${i === highlightIndex ? ' hs-highlight' : ''}">
      <span class="hs-rank">#${i + 1}</span>
      <span class="hs-name">${escapeHtml(s.name)}</span>
      <span class="hs-score">${s.score.toLocaleString()}</span>
      <span class="hs-meta">${s.lines}L &times;${s.maxCombo}</span>
    </div>`).join('');
}

// Core state
let board, current, next, score, lines, level, paused, gameOver, lastTime, dropAccum, dropInterval, animId;

// Hold
let heldPiece, holdUsed;

// Combo
let comboCount, maxCombo, lastClearWasTetris, lastActionWasRotate;

// Piece queue
let pieceQueue;
let powerUpLineThreshold;

// Active effects
let freezeActive, freezeEnd, slowActive, slowEnd;

// Energy / abilities
let energy, abilityMenuOpen;
let boardSnapshot, currentSnapshot;

// Starting level (persists across restarts)
let startingLevel = 1;

// Challenge mode
let gameMode = 'classic';
let sprintTimeLeft;
let survivalInterval, chaosFlipInterval;
let rotateDirection;

// ─── Piece factories ──────────────────────────────────────────────────────────

function makePiece(type) {
  const shape = PIECES[type].map(row => [...row]);
  return { type, shape, x: Math.floor(COLS / 2) - Math.floor(shape[0].length / 2), y: 0 };
}

function makePowerUpPiece() {
  const effects = ['bomb', 'lightning', 'dye', 'gravity', 'freeze'];
  const effect = effects[Math.floor(Math.random() * effects.length)];
  return { type: 13, shape: [[13, 13], [13, 13]], x: Math.floor(COLS / 2) - 1, y: 0, effect };
}

function generatePiece() {
  const r = Math.random();
  let type;
  if (r < 0.85)      type = Math.floor(Math.random() * 7) + 1;
  else if (r < 0.95) type = Math.floor(Math.random() * 3) + 8; // 8, 9, 10
  else               type = 12;
  return makePiece(type);
}

function refillQueue() {
  while (pieceQueue.length < 5) pieceQueue.push(generatePiece());
}

// ─── Core logic ───────────────────────────────────────────────────────────────

function createBoard() {
  return Array.from({ length: ROWS }, () => new Array(COLS).fill(0));
}

function collide(shape, ox, oy) {
  for (let r = 0; r < shape.length; r++) {
    for (let c = 0; c < shape[r].length; c++) {
      if (!shape[r][c]) continue;
      const nx = ox + c, ny = oy + r;
      if (nx < 0 || nx >= COLS || ny >= ROWS) return true;
      if (ny >= 0 && board[ny][nx]) return true;
    }
  }
  return false;
}

function rotateCW(shape) {
  const rows = shape.length, cols = shape[0].length;
  const out = Array.from({ length: cols }, () => new Array(rows).fill(0));
  for (let r = 0; r < rows; r++)
    for (let c = 0; c < cols; c++)
      out[c][rows - 1 - r] = shape[r][c];
  return out;
}

function rotateCCW(shape) {
  const rows = shape.length, cols = shape[0].length;
  const out = Array.from({ length: cols }, () => new Array(rows).fill(0));
  for (let r = 0; r < rows; r++)
    for (let c = 0; c < cols; c++)
      out[cols - 1 - c][r] = shape[r][c];
  return out;
}

function tryRotate() {
  const rotated = rotateDirection === 1 ? rotateCW(current.shape) : rotateCCW(current.shape);
  for (const kick of [0, -1, 1, -2, 2]) {
    if (!collide(rotated, current.x + kick, current.y)) {
      current.shape = rotated;
      current.x += kick;
      lastActionWasRotate = true;
      return;
    }
  }
}

function merge() {
  for (let r = 0; r < current.shape.length; r++)
    for (let c = 0; c < current.shape[r].length; c++)
      if (current.shape[r][c])
        board[current.y + r][current.x + c] = current.shape[r][c];
}

function clearLines() {
  let cleared = 0;
  for (let r = ROWS - 1; r >= 0; r--) {
    if (board[r].every(v => v !== 0)) {
      board.splice(r, 1);
      board.unshift(new Array(COLS).fill(0));
      cleared++;
      r++;
    }
  }
  if (cleared) {
    lines += cleared;
    score += (LINE_SCORES[cleared] || 0) * level;
    level = Math.floor(lines / 10) + 1;
    dropInterval = Math.max(100, 1000 - (level - 1) * 90);
    updateHUD();
  }
  return cleared;
}

function ghostY() {
  let gy = current.y;
  while (!collide(current.shape, current.x, gy + 1)) gy++;
  return gy;
}

function hardDrop() {
  const gy = ghostY();
  score += (gy - current.y) * 2;
  current.y = gy;
  lockPiece();
}

function softDrop() {
  if (!collide(current.shape, current.x, current.y + 1)) {
    current.y++;
    score += 1;
    updateHUD();
  } else {
    lockPiece();
  }
}

function lockPiece() {
  boardSnapshot = board.map(row => [...row]);
  currentSnapshot = { ...current, shape: current.shape.map(r => [...r]) };

  const isPowerUp = current.type === 13;
  const powerUpEffect = current.effect;
  const lockCX = current.x + Math.floor(current.shape[0].length / 2);
  const lockCY = current.y + Math.floor(current.shape.length / 2);

  merge();

  if (isPowerUp) {
    for (let r = 0; r < ROWS; r++)
      for (let c = 0; c < COLS; c++)
        if (board[r][c] === 13) board[r][c] = 0;
    applyPowerUp(powerUpEffect, lockCX, lockCY);
  }

  const linesCleared = clearLines();

  if (!isPowerUp && lines >= powerUpLineThreshold) {
    powerUpLineThreshold = lines + 10;
    pieceQueue.unshift(makePowerUpPiece());
    if (pieceQueue.length > 5) pieceQueue.pop();
    next = pieceQueue[0];
    drawNext();
  }

  if (linesCleared > 0) {
    comboCount++;
    if (comboCount > maxCombo) maxCombo = comboCount;
    if (comboCount >= 2) {
      score += 50 * comboCount * level;
      updateHUD();
    }

    if (current.type === 3 && lastActionWasRotate) {
      score += 400 * linesCleared * level;
      showAnnounce('T-SPIN!');
      updateHUD();
    }

    if (linesCleared === 4) {
      if (lastClearWasTetris) {
        score += 400;
        showAnnounce('B2B TETRIS!');
        updateHUD();
      } else {
        showAnnounce('TETRIS!');
      }
      lastClearWasTetris = true;
      pieceQueue.unshift(makePiece(11));
      if (pieceQueue.length > 5) pieceQueue.pop();
      next = pieceQueue[0];
      drawNext();
    } else {
      lastClearWasTetris = false;
    }

    if (board.every(row => row.every(v => v === 0))) {
      score += 3500 * level;
      showAnnounce('PERFECT CLEAR!');
      updateHUD();
    }

    energy = Math.min(MAX_ENERGY, energy + linesCleared * 20);
    updateEnergyBar();

    if (gameMode === 'sprint' && lines >= 40) {
      endGame('YOU WIN!', true);
      return;
    }
  } else {
    comboCount = 0;
  }

  updateComboDisplay();
  lastActionWasRotate = false;
  holdUsed = false;
  spawn();
}

function spawn() {
  current = pieceQueue.shift();
  refillQueue();
  next = pieceQueue[0];
  if (collide(current.shape, current.x, current.y)) {
    endGame();
    return;
  }
  drawNext();
  drawHold();
}

function doHold() {
  if (holdUsed || gameOver || paused) return;
  if (current.type === 13) return;

  if (heldPiece === null) {
    const src = PIECES[current.type];
    heldPiece = { type: current.type, shape: src.map(r => [...r]) };
    holdUsed = true;
    spawn();
  } else {
    const temp = heldPiece;
    const src = PIECES[current.type];
    heldPiece = { type: current.type, shape: src.map(r => [...r]) };
    const shape = temp.shape.map(r => [...r]);
    const x = Math.floor(COLS / 2) - Math.floor(shape[0].length / 2);
    current = { type: temp.type, shape, x, y: 0 };
    holdUsed = true;
    if (collide(current.shape, current.x, current.y)) {
      endGame();
      return;
    }
  }
  drawHold();
}

// ─── Power-up effects ─────────────────────────────────────────────────────────

function applyPowerUp(effect, cx, cy) {
  const labels = { bomb: 'BOMB!', lightning: 'LIGHTNING!', dye: 'DYE!', gravity: 'GRAVITY!', freeze: 'FREEZE!' };
  showAnnounce(labels[effect] || effect.toUpperCase() + '!');

  switch (effect) {
    case 'bomb':
      for (let r = cy - 1; r <= cy + 1; r++)
        for (let c = cx - 1; c <= cx + 1; c++)
          if (r >= 0 && r < ROWS && c >= 0 && c < COLS) board[r][c] = 0;
      break;

    case 'lightning':
      for (let r = 0; r < ROWS; r++) {
        if (board[r].some(v => v && v !== 13)) {
          board.splice(r, 1);
          board.unshift(new Array(COLS).fill(0));
          break;
        }
      }
      break;

    case 'dye': {
      const counts = new Array(13).fill(0);
      for (let r = 0; r < ROWS; r++)
        for (let c = 0; c < COLS; c++)
          if (board[r][c] >= 1 && board[r][c] <= 12) counts[board[r][c]]++;
      const dominant = counts.reduce((best, v, i) => v > counts[best] ? i : best, 1);
      const newColor = (dominant % 7) + 1;
      for (let r = 0; r < ROWS; r++)
        for (let c = 0; c < COLS; c++)
          if (board[r][c] === dominant) board[r][c] = newColor;
      break;
    }

    case 'gravity':
      for (let c = 0; c < COLS; c++) {
        const cells = [];
        for (let r = 0; r < ROWS; r++) if (board[r][c]) cells.push(board[r][c]);
        for (let r = 0; r < ROWS; r++)
          board[r][c] = r < ROWS - cells.length ? 0 : cells[r - (ROWS - cells.length)];
      }
      break;

    case 'freeze':
      freezeActive = true;
      freezeEnd = performance.now() + 5000;
      break;
  }
}

// ─── Challenge mode helpers ───────────────────────────────────────────────────

function addGarbageRow() {
  if (gameOver || paused) return;
  const gap = Math.floor(Math.random() * COLS);
  board.shift();
  board.push(Array.from({ length: COLS }, (_, c) => c === gap ? 0 : 5));
  if (collide(current.shape, current.x, current.y)) endGame();
}

function flipRotation() {
  if (gameOver) return;
  rotateDirection *= -1;
  showAnnounce(rotateDirection === 1 ? 'NORMAL ROTATION' : 'REVERSED!');
}

// ─── HUD / UI helpers ─────────────────────────────────────────────────────────

function updateHUD() {
  scoreEl.textContent = score.toLocaleString();
  linesEl.textContent = lines;
  levelEl.textContent = level;
}

function updateEnergyBar() {
  const bar = document.getElementById('energy-bar');
  const label = document.getElementById('energy-label');
  const pct = (energy / MAX_ENERGY) * 100;
  bar.style.width = pct + '%';
  const full = energy >= MAX_ENERGY;
  bar.classList.toggle('full', full);
  label.classList.toggle('energy-ready', full);
  label.textContent = full ? 'ENERGY (Q)' : 'ENERGY';
}

function updateComboDisplay() {
  const el = document.getElementById('combo-display');
  if (comboCount >= 2) {
    el.textContent = `COMBO x${comboCount}`;
    el.style.display = 'block';
    el.classList.remove('combo-pop');
    void el.offsetWidth;
    el.classList.add('combo-pop');
  } else {
    el.textContent = '';
    el.style.display = 'none';
    el.classList.remove('combo-pop');
  }
}

function updateSprintTimer() {
  const el = document.getElementById('sprint-timer');
  const t = Math.max(0, sprintTimeLeft);
  const mins = Math.floor(t / 60);
  const secs = Math.floor(t % 60);
  el.textContent = `${mins}:${secs.toString().padStart(2, '0')}`;
  el.classList.toggle('urgent', t <= 30);
}

let announceTimer = null;
function showAnnounce(text) {
  const el = document.getElementById('powerup-announce');
  el.textContent = text;
  el.classList.remove('announce-show');
  void el.offsetWidth;
  el.classList.add('announce-show');
  clearTimeout(announceTimer);
  announceTimer = setTimeout(() => el.classList.remove('announce-show'), 2200);
}

// ─── Rendering ────────────────────────────────────────────────────────────────

function drawBlock(context, x, y, colorIndex, size, alpha) {
  if (!colorIndex) return;
  let color;
  if (colorIndex === 13) {
    color = `hsl(${(Date.now() / 15) % 360}, 100%, 60%)`;
  } else {
    color = COLORS[colorIndex];
    if (!color) return;
  }
  context.globalAlpha = alpha ?? 1;
  context.fillStyle = color;
  context.fillRect(x * size + 1, y * size + 1, size - 2, size - 2);
  context.fillStyle = 'rgba(255,255,255,0.14)';
  context.fillRect(x * size + 1, y * size + 1, size - 2, 4);
  context.globalAlpha = 1;
}

function drawGrid() {
  ctx.strokeStyle = '#22222e';
  ctx.lineWidth = 0.5;
  for (let c = 1; c < COLS; c++) {
    ctx.beginPath(); ctx.moveTo(c * BLOCK, 0); ctx.lineTo(c * BLOCK, ROWS * BLOCK); ctx.stroke();
  }
  for (let r = 1; r < ROWS; r++) {
    ctx.beginPath(); ctx.moveTo(0, r * BLOCK); ctx.lineTo(COLS * BLOCK, r * BLOCK); ctx.stroke();
  }
}

function draw() {
  ctx.clearRect(0, 0, canvas.width, canvas.height);
  drawGrid();

  if (gameMode !== 'invisible') {
    for (let r = 0; r < ROWS; r++)
      for (let c = 0; c < COLS; c++)
        drawBlock(ctx, c, r, board[r][c], BLOCK);
  }

  if (gameMode !== 'invisible') {
    const gy = ghostY();
    for (let r = 0; r < current.shape.length; r++)
      for (let c = 0; c < current.shape[r].length; c++)
        if (current.shape[r][c])
          drawBlock(ctx, current.x + c, gy + r, current.shape[r][c], BLOCK, 0.2);
  }

  for (let r = 0; r < current.shape.length; r++)
    for (let c = 0; c < current.shape[r].length; c++)
      drawBlock(ctx, current.x + c, current.y + r, current.shape[r][c], BLOCK);
}

function drawPreview(context, canvasEl, piece) {
  const NB = 30;
  context.clearRect(0, 0, canvasEl.width, canvasEl.height);
  if (!piece) return;
  const shape = piece.shape;
  const offX = Math.floor((4 - shape[0].length) / 2);
  const offY = Math.floor((4 - shape.length) / 2);
  for (let r = 0; r < shape.length; r++)
    for (let c = 0; c < shape[r].length; c++)
      drawBlock(context, offX + c, offY + r, shape[r][c], NB);
}

function drawNext() { drawPreview(nextCtx, nextCanvas, next); }

function drawHold() {
  holdCanvas.classList.toggle('hold-locked', holdUsed);
  drawPreview(holdCtx, holdCanvas, heldPiece);
}

// ─── Ability menu ─────────────────────────────────────────────────────────────

function openAbilityMenu() {
  if (energy < MAX_ENERGY || gameOver || paused) return;
  abilityMenuOpen = true;
  cancelAnimationFrame(animId);
  document.getElementById('ability-menu').classList.remove('hidden');
}

function closeAbilityMenu() {
  document.getElementById('ability-menu').classList.add('hidden');
  abilityMenuOpen = false;
  energy = 0;
  updateEnergyBar();
  lastTime = performance.now();
  animId = requestAnimationFrame(loop);
}

function selectAbility(n) {
  switch (n) {
    case 1: {
      const names = pieceQueue.map(p => {
        const labels = ['I','O','T','S','Z','J','L','+','U','Y','1','□','★'];
        return labels[(p.type - 1)] || '?';
      });
      showAnnounce('NEXT: ' + names.join(' '));
      break;
    }
    case 2:
      current = generatePiece();
      break;
    case 3:
      slowActive = true;
      slowEnd = performance.now() + 10000;
      showAnnounce('SLOW TIME!');
      break;
    case 4:
      if (boardSnapshot) {
        board = boardSnapshot;
        current = currentSnapshot;
        updateHUD();
        showAnnounce('UNDO!');
      }
      break;
    case 5:
      holdUsed = false;
      drawHold();
      showAnnounce('HOLD UNLOCKED!');
      break;
  }
  closeAbilityMenu();
}

// ─── Game lifecycle ───────────────────────────────────────────────────────────

function endGame(title, win) {
  gameOver = true;
  cancelAnimationFrame(animId);
  if (survivalInterval) { clearInterval(survivalInterval); survivalInterval = null; }
  if (chaosFlipInterval) { clearInterval(chaosFlipInterval); chaosFlipInterval = null; }

  overlayTitle.textContent = title || 'GAME OVER';
  overlayTitle.classList.toggle('win', !!win);
  overlayScore.textContent = `Score: ${score.toLocaleString()}`;
  document.getElementById('overlay-stats').textContent =
    `Lines: ${lines}  |  Best combo: \xd7${maxCombo}`;

  const newRecordSection = document.getElementById('new-record-section');
  const nameInput = document.getElementById('player-name');
  if (isTopScore(score)) {
    newRecordSection.classList.remove('hidden');
    nameInput.value = '';
    setTimeout(() => nameInput.focus(), 50);
  } else {
    newRecordSection.classList.add('hidden');
  }

  renderScoreTable('gameover-hs-table', null);
  overlay.classList.remove('hidden');
}

function togglePause() {
  if (gameOver) return;
  paused = !paused;
  const pauseMenu = document.getElementById('pause-menu');
  if (!paused) {
    pauseMenu.classList.add('hidden');
    lastTime = performance.now();
    animId = requestAnimationFrame(loop);
  } else {
    cancelAnimationFrame(animId);
    document.getElementById('pause-controls').classList.add('hidden');
    document.getElementById('controls-toggle-btn').textContent = 'VIEW CONTROLS';
    pauseMenu.classList.remove('hidden');
  }
}

function loop(ts) {
  const dt = ts - lastTime;
  lastTime = ts;

  if (gameMode === 'sprint') {
    sprintTimeLeft -= dt / 1000;
    updateSprintTimer();
    if (sprintTimeLeft <= 0 && !gameOver) {
      endGame('TIME\'S UP!');
      return;
    }
  }

  if (freezeActive && ts > freezeEnd) freezeActive = false;
  if (slowActive && ts > slowEnd) slowActive = false;

  let effectiveInterval = dropInterval;
  if (freezeActive) effectiveInterval = 1000;
  else if (slowActive) effectiveInterval = Math.min(dropInterval * 2, 2000);

  dropAccum += dt;
  if (dropAccum >= effectiveInterval) {
    dropAccum = 0;
    if (!collide(current.shape, current.x, current.y + 1)) {
      current.y++;
    } else {
      lockPiece();
    }
  }

  if (gameOver) return;
  draw();
  animId = requestAnimationFrame(loop);
}

function init() {
  board        = createBoard();
  score        = 0;
  lines        = 0;
  level        = startingLevel;
  paused       = false;
  gameOver     = false;
  dropInterval = Math.max(100, 1000 - (startingLevel - 1) * 90);
  dropAccum    = 0;
  lastTime     = performance.now();

  heldPiece   = null;
  holdUsed    = false;

  comboCount          = 0;
  maxCombo            = 0;
  lastClearWasTetris  = false;
  lastActionWasRotate = false;

  pieceQueue           = [];
  powerUpLineThreshold = 10;
  refillQueue();

  freezeActive = false;
  slowActive   = false;
  energy       = 0;
  abilityMenuOpen  = false;
  boardSnapshot    = null;
  currentSnapshot  = null;
  rotateDirection  = 1;

  if (survivalInterval)  { clearInterval(survivalInterval);  survivalInterval  = null; }
  if (chaosFlipInterval) { clearInterval(chaosFlipInterval); chaosFlipInterval = null; }

  const sprintSection = document.getElementById('sprint-section');
  if (gameMode === 'sprint') {
    sprintTimeLeft = 120;
    sprintSection.style.display = 'flex';
    updateSprintTimer();
  } else {
    sprintSection.style.display = 'none';
  }
  if (gameMode === 'survival') {
    survivalInterval = setInterval(addGarbageRow, 10000);
  }
  if (gameMode === 'chaos') {
    chaosFlipInterval = setInterval(flipRotation, 20000);
  }

  document.getElementById('mode-label').textContent = gameMode.toUpperCase();
  document.getElementById('ability-menu').classList.add('hidden');
  document.getElementById('pause-menu').classList.add('hidden');
  overlay.classList.add('hidden');
  overlayTitle.classList.remove('win');

  next = pieceQueue[0];
  updateEnergyBar();
  updateComboDisplay();
  spawn();
  updateHUD();
  drawHold();

  cancelAnimationFrame(animId);
  animId = requestAnimationFrame(loop);
}

function selectMode(mode) {
  gameMode = mode;
  document.getElementById('mode-select').classList.add('hidden');
  init();
}

// ─── Event listeners ──────────────────────────────────────────────────────────

document.addEventListener('keydown', e => {
  if (!board) return;

  if (abilityMenuOpen) {
    const n = parseInt(e.key);
    if (n >= 1 && n <= 5) selectAbility(n);
    return;
  }

  if (e.code === 'KeyP' || e.code === 'Escape') { e.preventDefault(); togglePause(); return; }
  if (paused || gameOver) return;

  switch (e.code) {
    case 'ArrowLeft':
      if (!collide(current.shape, current.x - 1, current.y)) {
        current.x--;
        lastActionWasRotate = false;
      }
      break;
    case 'ArrowRight':
      if (!collide(current.shape, current.x + 1, current.y)) {
        current.x++;
        lastActionWasRotate = false;
      }
      break;
    case 'ArrowDown':
      softDrop();
      break;
    case 'ArrowUp':
    case 'KeyX':
      tryRotate();
      break;
    case 'Space':
      e.preventDefault();
      hardDrop();
      break;
    case 'KeyC':
    case 'ShiftLeft':
    case 'ShiftRight':
      doHold();
      break;
    case 'KeyQ':
      openAbilityMenu();
      break;
  }
  updateHUD();
});

restartBtn.addEventListener('click', init);

document.getElementById('resume-btn').addEventListener('click', togglePause);

document.getElementById('pause-restart-btn').addEventListener('click', () => {
  document.getElementById('pause-menu').classList.add('hidden');
  paused = false;
  init();
});

document.getElementById('controls-toggle-btn').addEventListener('click', () => {
  const el = document.getElementById('pause-controls');
  const nowHidden = el.classList.toggle('hidden');
  document.getElementById('controls-toggle-btn').textContent = nowHidden ? 'VIEW CONTROLS' : 'HIDE CONTROLS';
});

document.getElementById('level-dec').addEventListener('click', () => {
  if (startingLevel > 1) {
    startingLevel--;
    document.getElementById('starting-level-display').textContent = startingLevel;
  }
});

document.getElementById('level-inc').addEventListener('click', () => {
  if (startingLevel < 15) {
    startingLevel++;
    document.getElementById('starting-level-display').textContent = startingLevel;
  }
});

document.querySelectorAll('.mode-btn').forEach(btn => {
  btn.addEventListener('click', () => selectMode(btn.dataset.mode));
});

document.querySelectorAll('.ability-btn').forEach(btn => {
  btn.addEventListener('click', () => selectAbility(parseInt(btn.dataset.ability)));
});

function saveCurrentScore() {
  const nameInput = document.getElementById('player-name');
  const name = nameInput.value.trim() || 'ANON';
  const entry = { name, score, lines, maxCombo, mode: gameMode, ts: Date.now() };
  const idx = addScore(entry);
  document.getElementById('new-record-section').classList.add('hidden');
  renderScoreTable('gameover-hs-table', idx);
}

document.getElementById('save-score-btn').addEventListener('click', saveCurrentScore);

document.getElementById('player-name').addEventListener('keydown', e => {
  if (e.key === 'Enter') saveCurrentScore();
});

document.getElementById('reset-scores-btn').addEventListener('click', () => {
  localStorage.removeItem('tetris_scores');
  renderScoreTable('start-hs-table', null);
});

renderScoreTable('start-hs-table', null);
