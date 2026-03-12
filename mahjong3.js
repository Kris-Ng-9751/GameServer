// ══════════════════════════════════════════════════════════════
// game3p.js — 三人麻將主遊戲邏輯
//
// 三人規則差異（相較於 game.js 四人版）：
//   - 僅東·南·西 三家，無北家（AI_NORTH 不存在）
//   - 牌山：僅筒子(P) + 字牌(Z1-Z3,Z5-Z7) + 花(F1-F8,F13-F16) + 飛，共 76 張
//     （無萬子/條子/北風 Z4/琴棋書畫 F9-F12）
//   - 無吃牌（禁吃）
//   - 自摸：兩家各賠全額（非各賠半額）
//   - 榮胡：僅打牌者賠全額
//
// 依賴：mahjong-core.js（window.MJ）
// 對應 HTML：three-player.html
// ══════════════════════════════════════════════════════════════

// ── 三人麻將版 game3p.js ──────────────────────────────────────────
// 規則：東·南·西 三家對局；移除北風牌(Z4)；無吃牌；
//       自摸→兩家各賠全額；榮胡→僅打牌者賠
// ─────────────────────────────────────────────────────────────────
const MJ = window.MJ;

/* ── 座位 ID 常量（三人版，無北家）── */
const PLAYER_SOUTH = "S"; // 你（南家）
const AI_EAST = "E";      // 人機 2（東家）
const AI_WEST = "W";      // 人機 1（西家）
// 三人麻將：無北家 (AI_NORTH 不存在)

// ── 座位全名（骰子/日誌顯示用）── 須在 PLAYER_SOUTH/AI_EAST/AI_WEST 之後定義
const SEAT_NAMES_FULL = {
  [PLAYER_SOUTH]: "南家（你）", // 動態由 playerName 覆蓋
  [AI_EAST]:      "人機 2",
  [AI_WEST]:      "人機 1",
};
const DIE_CHARS = ["⚀","⚁","⚂","⚃","⚄","⚅"];
// 三人骰子順序：依骰子點數 mod 3 對應座位（南·東·西）
const DICE_SEAT_ORDER = [PLAYER_SOUTH, AI_EAST, AI_WEST];

// 三人麻將牌山特殊規則：
//   ・無萬子（M1-M9）
//   ・無條子（S1-S9）
//   ・無北風（Z4）
//   ・無琴棋書畫花（F9-F12）
//   剩餘：筒子P×36 + 字牌Z1-Z3,Z5-Z7×24 + 花F1-F8,F13-F16×12 + 飛H×4 = 76 張
function createThreePlayerWall() {
  return MJ.createFullWall().filter(t => {
    if (t[0] === "M") return false;                         // 無萬子
    if (t[0] === "S") return false;                         // 無條子
    if (t === "Z4")   return false;                         // 無北風
    if (t[0] === "F") {
      const n = parseInt(t.slice(1));
      if (n >= 9 && n <= 12) return false;                  // 無琴棋書畫
    }
    return true;
  });
}

/* ══════════════════════════════════════════════════════════════
   全局遊戲狀態（三人版，僅三家）
   ══════════════════════════════════════════════════════════════ */
let wall = [];          // 剩餘牌山（76 張特殊牌庫）
let hands = {           // 三家手牌
  [PLAYER_SOUTH]: [],
  [AI_EAST]: [],
  [AI_WEST]: [],
};
let discards = {        // 三家棄牌記錄
  [PLAYER_SOUTH]: [],
  [AI_EAST]: [],
  [AI_WEST]: [],
};
let flowers = {         // 三家花牌
  [PLAYER_SOUTH]: [],
  [AI_EAST]: [],
  [AI_WEST]: [],
};
let feis = {            // 三家飛牌（萬用牌）
  [PLAYER_SOUTH]: [],
  [AI_EAST]: [],
  [AI_WEST]: [],
};
let melds = {           // 三家副露
  [PLAYER_SOUTH]: [],
  [AI_EAST]: [],
  [AI_WEST]: [],
};

let lastDiscard = null;          // 最後一張棄牌 { tile, from }
let awaitingPlayerClaim = false; // 是否正等待玩家選擇搶牌

// ── 籌碼系統 ────────────────────────────────────────────────────
const INITIAL_SCORE = 10000;
let BASE_UNIT       = 100;   // 1番 = N 分（由賠率選擇器設定）

// ── 從 localStorage 恢復玩家資料（手機版 ↔ PC 版同步）──
const _savedName    = localStorage.getItem("mj-player-name");
const _savedAvatar  = localStorage.getItem("mj-player-avatar");
let scores = {
  [PLAYER_SOUTH]: INITIAL_SCORE,
  [AI_EAST]:      INITIAL_SCORE,
  [AI_WEST]:      INITIAL_SCORE,
};
let claimOptions = { chi: false, peng: false, gang: false, chiOptions: [] };
let kbdSelIdx = -1; // 鍵盤方向鍵選中的手牌索引（-1 = 未選）
let currentTurn = PLAYER_SOUTH;
let dealerPlayer = PLAYER_SOUTH; // 本局庄家（先手）
let drawnThisTurn = false;
let gameOver = false;
let afterKongDraw = false; // 槓後補牌（嶺上開花用）
let turnCount = 0;         // 第幾輪（天胡/地胡用）
let pendingTurnAfterDiscard = null; // 搶牌窗口打開時，記住自然輪轉的下一家
let dragSrcIdx = -1;               // 手牌拖拽排序用
let sessionOver = false;           // 有玩家籌碼耗盡，本場結束
let playerName    = _savedName   || "玩家"; // 玩家自訂名字（持久化）
let playerAvatar  = _savedAvatar || "🀄";  // 玩家頭像（持久化）
let nameConfirmed = !!_savedName;          // 已輸入過名字
let allMuted = localStorage.getItem("all-muted") === "true"; // 全部靜音
let aiDifficulty = localStorage.getItem("ai-difficulty") || "normal"; // 人機難度

/* ══════════════════════════════════════════════════════════════
   DOM 元素快取（三人版，無北家 DOM 元素）
   ══════════════════════════════════════════════════════════════ */
const elPlayerHand = document.getElementById("player-hand");
const elAiEastHand = document.getElementById("ai-east-hand");
const elAiWestHand = document.getElementById("ai-west-hand");
// 三人麻將：無北家，不引用北家 DOM 元素
const elDiscardSouth = document.getElementById("discard-south");
const elDiscardEast = document.getElementById("discard-east");
const elDiscardWest = document.getElementById("discard-west");
const elFlowersSouth = document.getElementById("flowers-south");
const elFlowersEast = document.getElementById("flowers-east");
const elFlowersWest = document.getElementById("flowers-west");
const elFeisSouth = document.getElementById("feis-south");
const elFeisEast = document.getElementById("feis-east");
const elFeisWest = document.getElementById("feis-west");
const elMeldsSouth = document.getElementById("melds-south");
const elMeldsEast = document.getElementById("melds-east");
const elMeldsWest = document.getElementById("melds-west");
const elWallCount     = document.getElementById("wall-count");
const elWallCountBar  = document.getElementById("wall-count-bar");
const elCurrentPlayer = document.getElementById("current-player");
const topBar = document.getElementById("top-bar");

function showTopBar() { topBar && topBar.classList.add("visible"); }
function hideTopBar() { topBar && topBar.classList.remove("visible"); }

// ── 人機難度選擇 UI ────────────────────────────────────────────────
(function initDifficultySelector() {
  const btns = document.querySelectorAll(".diff-btn");
  btns.forEach(btn => {
    // 初始化高亮
    btn.classList.toggle("diff-btn-active", btn.dataset.diff === aiDifficulty);
    btn.addEventListener("click", () => {
      aiDifficulty = btn.dataset.diff;
      localStorage.setItem("ai-difficulty", aiDifficulty);
      btns.forEach(b => b.classList.toggle("diff-btn-active", b.dataset.diff === aiDifficulty));
    });
  });
})();

// ── 難度相關：AI 弃牌策略 ─────────────────────────────────────────
// 簡單：隨機丟牌（真正會出錯）
function chooseAiDiscardEasy(hand) {
  const nonFei = hand.filter(t => t[0] !== "H");
  if (nonFei.length === 0) return hand[0];
  return nonFei[Math.floor(Math.random() * nonFei.length)];
}

// 困難：評估每種弃牌後的手牌品質，選最優
function evaluateHandScore(hand) {
  if (MJ.isWinningHand(hand)) return 1000;
  const nonFei = hand.filter(t => t[0] !== "H");
  const feiCnt = hand.length - nonFei.length;
  const cnt = {};
  for (const t of nonFei) cnt[t] = (cnt[t] || 0) + 1;
  let score = feiCnt * 3; // 飛牌保留加分
  // 刻子 / 對子
  for (const [, c] of Object.entries(cnt)) {
    if (c >= 3) score += 8;
    else if (c === 2) score += 4;
  }
  // 完整順子 / 半順（三人版：只有筒子 P）
  for (const s of ["P"]) {
    for (let v = 1; v <= 7; v++) {
      const has = (x) => (cnt[`${s}${x}`] || 0) > 0;
      if (has(v) && has(v+1) && has(v+2)) score += 7;
      else if ((has(v) && has(v+1)) || (has(v) && has(v+2)) || (has(v+1) && has(v+2))) score += 2;
    }
  }
  return score;
}
function chooseAiDiscardHard(hand) {
  const nonFei = hand.filter(t => t[0] !== "H");
  if (nonFei.length === 0) return hand[0];
  let best = null, bestScore = -Infinity;
  const seen = new Set();
  for (const tile of nonFei) {
    if (seen.has(tile)) continue;
    seen.add(tile);
    const remaining = [...hand];
    remaining.splice(remaining.indexOf(tile), 1);
    const s = evaluateHandScore(remaining);
    if (s > bestScore) { bestScore = s; best = tile; }
  }
  return best || MJ.chooseAiDiscard(hand);
}

// 統一出口：根據難度選擇 AI 弃牌函數
function chooseAiDiscardByDifficulty(hand) {
  if (aiDifficulty === "easy")   return chooseAiDiscardEasy(hand);
  if (aiDifficulty === "hard")   return chooseAiDiscardHard(hand);
  return MJ.chooseAiDiscard(hand); // normal
}

// 難度相關：AI 是否執行搶牌（簡單有概率跳過）
function aiShouldClaim(type) {
  if (aiDifficulty !== "easy") return true;
  if (type === "gang")  return Math.random() < 0.80;
  if (type === "peng")  return Math.random() < 0.60;
  if (type === "chi")   return Math.random() < 0.50;
  return true;
}

// 困難：AI 吃牌前先評估是否有益（吃後手牌分數比不吃高才吃）
function aiShouldChi(ai, tile, from) {
  if (aiDifficulty === "easy") return Math.random() < 0.50;
  if (aiDifficulty === "normal") return true;
  // hard：評估吃後的最佳弃牌
  const suit = tile[0], v = parseInt(tile.slice(1), 10);
  if (suit === "Z" || suit === "F" || suit === "H") return false;
  const has = (val) => hands[ai].some(t => t === `${suit}${val}`);
  const combos = [];
  if (v >= 3 && has(v-2) && has(v-1)) combos.push([`${suit}${v-2}`, `${suit}${v-1}`, tile]);
  if (v >= 2 && v <= 8 && has(v-1) && has(v+1)) combos.push([`${suit}${v-1}`, tile, `${suit}${v+1}`]);
  if (v <= 7 && has(v+1) && has(v+2)) combos.push([tile, `${suit}${v+1}`, `${suit}${v+2}`]);
  if (combos.length === 0) return false;
  const basePre = evaluateHandScore(hands[ai]);
  for (const combo of combos) {
    const afterHand = [...hands[ai]];
    for (const t of combo) { const i = afterHand.indexOf(t); if (i !== -1) afterHand.splice(i, 1); }
    afterHand.push(tile);
    const discard = chooseAiDiscardHard(afterHand);
    const afterDiscard = [...afterHand];
    afterDiscard.splice(afterDiscard.indexOf(discard), 1);
    if (evaluateHandScore(afterDiscard) > basePre) return true;
  }
  return false;
}

// ── 牌桌自適應縮放：讓 .table 自動縮放至可用視窗 ──────────────
function fitTable() {
  const wrapper = document.querySelector(".table-wrapper");
  const table   = document.querySelector(".table");
  if (!wrapper || !table) return;

  // 重置 scale 以量取自然尺寸
  wrapper.style.transform = "";
  wrapper.style.height    = "";

  const topBarH  = (topBar && topBar.offsetHeight) || 52;
  const availW   = window.innerWidth  - 24;           // 左右各留 12px
  const availH   = window.innerHeight - topBarH - 16; // 頂欄 + 底部留白

  const naturalW = table.offsetWidth;
  const naturalH = table.offsetHeight;
  if (!naturalW || !naturalH) return;

  const scale = Math.min(1, availW / naturalW, availH / naturalH);

  if (scale < 0.999) {
    wrapper.style.transform = `scale(${scale.toFixed(4)})`;
    // 壓縮後高度折疊，避免頁面出現多餘空白
    wrapper.style.height = Math.round(naturalH * scale) + "px";
  }
}
window.addEventListener("resize", fitTable);

// ── 胡牌記錄（記憶體暫存：跨局保留，重新整理頁面後清空；刻意不用 localStorage）──
const winHistory = [];
const elLog = document.getElementById("log");
const btnNewGame = document.getElementById("btn-new-game");
const btnDraw      = document.getElementById("btn-draw");
const btnWin       = document.getElementById("btn-win");
const btnChi       = document.getElementById("btn-chi"); // null in 3-player HTML
const btnPeng      = document.getElementById("btn-peng");
const btnGang      = document.getElementById("btn-gang");
const btnSwapFei   = document.getElementById("btn-swap-fei");
const btnTenpai    = document.getElementById("btn-tenpai");
const btnPass      = document.getElementById("btn-pass");
const btnRecommend = document.getElementById("btn-recommend");

btnNewGame.addEventListener("click", () => {
  if (sessionOver) { goHomeAfterBankrupt(); } else { startNewGame(); }
});
if (btnDraw) btnDraw.addEventListener("click", onPlayerDraw);
btnWin.addEventListener("click", onPlayerWinAttempt);
// 三人麻將：無吃牌，btnChi 在 HTML 不存在
if (btnChi) btnChi.addEventListener("click", onPlayerChi);
btnPeng.addEventListener("click", onPlayerPeng);
btnGang.addEventListener("click", onPlayerGang);
btnSwapFei.addEventListener("click", onSwapFei);
btnTenpai.addEventListener("click", showTenpaiOverlay);
btnPass.addEventListener("click", onPlayerPass);
if (btnRecommend) btnRecommend.addEventListener("click", showRecommendation);
document.getElementById("btn-tenpai-close").addEventListener("click", () => {
  document.getElementById("tenpai-overlay").style.display = "none";
});
document.getElementById("btn-recommend-close").addEventListener("click", clearRecommend);
document.getElementById("recommend-overlay").addEventListener("click", (e) => {
  if (e.target === e.currentTarget) clearRecommend();
});
document.getElementById("btn-close-win").addEventListener("click", () => {
  document.getElementById("win-overlay").classList.add("hidden");
  if (sessionOver) {
    goHomeAfterBankrupt();
  } else {
    startNewGame();
  }
});

// 主頁面：開始遊戲
document.getElementById("btn-start-game").addEventListener("click", () => {
  document.getElementById("home-screen").classList.add("hidden");
  showTopBar();
  startNewGame();
});

// 主頁右側菜單：遊戲介面預覽（三人版：該按鈕不存在，安全跳過）
const _previewBtn = document.getElementById("btn-home-preview");
if (_previewBtn) _previewBtn.addEventListener("click", () => {
  const modal  = document.getElementById("game-preview-modal");
  const wrap   = document.getElementById("game-preview-scale-wrap");
  const gameEl = document.getElementById("app");

  // ── 1. 保存當前遊戲狀態 ──
  const _savedState = {
    wall:       [...wall],
    hands:      { S: [...hands[PLAYER_SOUTH]], E: [...hands[AI_EAST]], W: [...hands[AI_WEST]] },
    discards:   { S: [...discards[PLAYER_SOUTH]], E: [...discards[AI_EAST]], W: [...discards[AI_WEST]] },
    flowers:    { S: [...flowers[PLAYER_SOUTH]], E: [...flowers[AI_EAST]], W: [...flowers[AI_WEST]] },
    melds:      { S: [...melds[PLAYER_SOUTH]], E: [...melds[AI_EAST]], W: [...melds[AI_WEST]] },
    currentTurn, dealerPlayer, drawnThisTurn, gameOver, awaitingPlayerClaim, lastDiscard,
  };

  // ── 2. 注入示例牌面（三人版：只有筒子、字牌）──
  const DEMO_SOUTH = ["P1","P2","P3","P4","P5","P6","P7","P8","P9","Z1","Z1","Z5","Z5","P3"];
  const DEMO_DISC_S = ["Z3","P1","Z6","Z3","P7"];
  const DEMO_DISC_E = ["P2","Z5","P6","Z6","P9"];
  const DEMO_DISC_W = ["P1","Z3","P7","Z1","P6"];
  hands[PLAYER_SOUTH] = [...DEMO_SOUTH];
  hands[AI_EAST]  = Array(13).fill("?");
  hands[AI_WEST]  = Array(13).fill("?");
  discards[PLAYER_SOUTH] = DEMO_DISC_S;
  discards[AI_EAST]      = DEMO_DISC_E;
  discards[AI_WEST]      = DEMO_DISC_W;
  flowers[PLAYER_SOUTH] = ["F1"];
  flowers[AI_EAST] = flowers[AI_WEST] = [];
  melds[PLAYER_SOUTH] = melds[AI_EAST] = melds[AI_WEST] = [];
  wall = Array(60).fill("?");
  currentTurn = PLAYER_SOUTH;
  dealerPlayer = AI_WEST;
  drawnThisTurn = true;
  gameOver = false;
  awaitingPlayerClaim = false;
  lastDiscard = null;

  // ── 3. 渲染示例狀態，讓 #app 可見 ──
  gameEl.style.display = "block";
  render();

  // ── 4. 量取尺寸並克隆 ──
  const origW = gameEl.scrollWidth  || 900;
  const origH = gameEl.scrollHeight || 600;
  const scale = Math.min(
    (window.innerWidth  * 0.88) / origW,
    (window.innerHeight * 0.78) / origH,
    0.72
  );
  wrap.style.width  = Math.round(origW * scale) + "px";
  wrap.style.height = Math.round(origH * scale) + "px";

  wrap.innerHTML = "";
  const inner = document.createElement("div");
  inner.className = "game-preview-scale-inner";
  inner.style.width     = origW + "px";
  inner.style.height    = origH + "px";
  inner.style.transform = `scale(${scale})`;
  const cloned = gameEl.cloneNode(true);
  cloned.style.display = "block";
  cloned.style.pointerEvents = "none";
  inner.appendChild(cloned);
  wrap.appendChild(inner);

  // ── 5. 恢復原始狀態 ──
  wall = _savedState.wall;
  hands[PLAYER_SOUTH] = _savedState.hands.S;
  hands[AI_EAST]  = _savedState.hands.E;
  hands[AI_WEST]  = _savedState.hands.W;
  discards[PLAYER_SOUTH] = _savedState.discards.S;
  discards[AI_EAST]  = _savedState.discards.E;
  discards[AI_WEST]  = _savedState.discards.W;
  flowers[PLAYER_SOUTH] = _savedState.flowers.S;
  flowers[AI_EAST]  = _savedState.flowers.E;
  flowers[AI_WEST]  = _savedState.flowers.W;
  melds[PLAYER_SOUTH] = _savedState.melds.S;
  melds[AI_EAST]  = _savedState.melds.E;
  melds[AI_WEST]  = _savedState.melds.W;
  currentTurn = _savedState.currentTurn;
  dealerPlayer = _savedState.dealerPlayer;
  drawnThisTurn = _savedState.drawnThisTurn;
  gameOver = _savedState.gameOver;
  awaitingPlayerClaim = _savedState.awaitingPlayerClaim;
  lastDiscard = _savedState.lastDiscard;
  gameEl.style.display = "";
  if (!gameOver && hands[PLAYER_SOUTH].length > 0) render();

  modal.classList.remove("hidden");
}); // end _previewBtn

const _closePreviewBtn = document.getElementById("btn-close-preview");
if (_closePreviewBtn) _closePreviewBtn.addEventListener("click", () => {
  document.getElementById("game-preview-modal").classList.add("hidden");
});
const _previewModal = document.getElementById("game-preview-modal");
if (_previewModal) _previewModal.addEventListener("click", (e) => {
  if (e.target === e.currentTarget || e.target.classList.contains("game-preview-backdrop")) {
    document.getElementById("game-preview-modal").classList.add("hidden");
  }
});

// 賠率按鈕切換
document.getElementById("rate-options").addEventListener("click", (e) => {
  const btn = e.target.closest(".rate-btn");
  if (!btn) return;
  document.querySelectorAll(".rate-btn").forEach(b => b.classList.remove("active"));
  btn.classList.add("active");
});

// 看牌：主頁顯示所有牌型
document.getElementById("btn-view-tiles").addEventListener("click", showTileRefOverlay);
document.getElementById("btn-tile-ref-close").addEventListener("click", () => {
  document.getElementById("tile-ref-overlay").style.display = "none";
});

// ── 麻將教學 overlay ──
(function() {
  const overlay = document.getElementById("tutorial-overlay");
  if (!overlay) return;

  let tilesRendered = false;
  function renderTutorialTiles() {
    if (tilesRendered) return;
    tilesRendered = true;
    overlay.querySelectorAll(".tut-tile-row[data-tiles]").forEach(row => {
      row.innerHTML = "";
      row.dataset.tiles.split(" ").forEach(code => {
        const el = renderTile(code, false);
        el.classList.add("tut-real-tile");
        row.appendChild(el);
      });
    });
  }

  function openTutorial() {
    overlay.style.display = "flex";
    renderTutorialTiles();
  }
  function closeTutorial() { overlay.style.display = "none"; }

  overlay.querySelectorAll(".tutorial-tab").forEach(tab => {
    tab.addEventListener("click", () => {
      overlay.querySelectorAll(".tutorial-tab").forEach(t => t.classList.remove("active"));
      overlay.querySelectorAll(".tutorial-page").forEach(p => p.classList.remove("active"));
      tab.classList.add("active");
      const page = overlay.querySelector(`.tutorial-page[data-page="${tab.dataset.tab}"]`);
      if (page) page.classList.add("active");
    });
  });

  const btnOpen = document.getElementById("btn-home-tutorial");
  if (btnOpen) btnOpen.addEventListener("click", openTutorial);
  const btnClose = document.getElementById("btn-tutorial-close");
  if (btnClose) btnClose.addEventListener("click", closeTutorial);
  overlay.addEventListener("click", e => { if (e.target === overlay) closeTutorial(); });
})();

// ── 鍵盤操作說明 overlay ──
function showKbdOverlay() {
  const el = document.getElementById("kbd-overlay");
  if (el) el.style.display = "flex";
}
const _btnHomeKbd = document.getElementById("btn-home-kbd");
if (_btnHomeKbd) _btnHomeKbd.addEventListener("click", showKbdOverlay);
const _btnKbdClose = document.getElementById("btn-kbd-close");
if (_btnKbdClose) _btnKbdClose.addEventListener("click", () => {
  document.getElementById("kbd-overlay").style.display = "none";
});
const _kbdOverlay = document.getElementById("kbd-overlay");
if (_kbdOverlay) _kbdOverlay.addEventListener("click", (e) => {
  if (e.target === e.currentTarget) e.currentTarget.style.display = "none";
});

// ── 胡牌規則 overlay ──
const YAKU_SECTIONS = [
  {
    title: "🎯 特殊胡法",
    items: [
      { name:"天胡",   cls:"yr-special", desc:"庄家起手第一摸即胡",         tiles:[] },
      { name:"地胡",   cls:"yr-special", desc:"閒家第一輪摸牌即胡",         tiles:[] },
      { name:"嶺上開花",cls:"yr-special",desc:"槓牌後補牌自摸胡",           tiles:[] },
      { name:"自摸",   cls:"",           desc:"摸牌自行完成胡牌",           tiles:[] },
      { name:"榮胡",   cls:"",           desc:"對別人打出的牌宣胡",         tiles:[] },
    ]
  },
  {
    title: "🀄 基本牌型",
    items: [
      { name:"普通胡", cls:"", desc:"4組面子＋1組將牌",
        tiles:[["M1","M2","M3"],["P5","P5","P5"],["S7","S8","S9"],["M4","M5","M6"],["Z1","Z1"]] },
      { name:"平胡",   cls:"", desc:"全順子，將牌非字牌，無副露",
        tiles:[["M1","M2","M3"],["M4","M5","M6"],["P3","P4","P5"],["S6","S7","S8"],["M8","M8"]] },
      { name:"碰碰胡", cls:"", desc:"所有面子均為刻子（三張相同）",
        tiles:[["M1","M1","M1"],["P5","P5","P5"],["S9","S9","S9"],["M9","M9","M9"],["Z1","Z1"]] },
      { name:"門前清", cls:"", desc:"無任何副露（碰/吃/槓）",             tiles:[] },
      { name:"斷幺",   cls:"", desc:"全手牌為 2–8，無么九及字牌",
        tiles:[["M2","M3","M4"],["P5","P6","P7"],["S3","S4","S5"],["M6","M7","M8"],["P4","P4"]] },
      { name:"全帶幺", cls:"", desc:"每組面子/將牌均含么九或字牌",
        tiles:[["M1","M2","M3"],["M9","M9","M9"],["Z1","Z1","Z1"],["P1","P2","P3"],["M9","M9"]] },
      { name:"純全帶幺",cls:"",desc:"每組面子/將牌均含么九，無字牌",
        tiles:[["M1","M2","M3"],["M9","M9","M9"],["S1","S2","S3"],["P7","P8","P9"],["M1","M1"]] },
      { name:"全求人", cls:"", desc:"全部靠榮胡副露，且無暗刻",           tiles:[] },
    ]
  },
  {
    title: "🌊 花色役",
    items: [
      { name:"清一色", cls:"yr-flush", desc:"全手牌同一花色，無字牌",
        tiles:[["M1","M2","M3"],["M4","M5","M6"],["M7","M8","M9"],["M2","M3","M4"],["M5","M5"]] },
      { name:"混一色", cls:"",         desc:"同一花色＋字牌混入",
        tiles:[["M1","M2","M3"],["M4","M5","M6"],["Z1","Z1","Z1"],["Z2","Z2","Z2"],["M7","M7"]] },
      { name:"字一色", cls:"yr-special",desc:"全部字牌（東南西北中發白）",
        tiles:[["Z1","Z1","Z1"],["Z2","Z2","Z2"],["Z3","Z3","Z3"],["Z5","Z5","Z5"],["Z4","Z4"]] },
    ]
  },
  {
    title: "✨ 特殊牌型",
    items: [
      { name:"七對",   cls:"yr-special", desc:"無副露，7組對子（飛牌可補）",
        tiles:[["M1","M1"],["M3","M3"],["P2","P2"],["S4","S4"],["Z1","Z1"],["Z2","Z2"],["M7","M7"]] },
      { name:"十三幺", cls:"yr-special", desc:"含各花色1、9及全部字牌各一，加任一重複",
        tiles:[["M1","M9","P1","P9","S1","S9","Z1","Z2","Z3","Z4","Z5","Z6","Z7","M1"]] },
      { name:"清么九", cls:"yr-special", desc:"所有牌皆為么九牌（1、9），無字牌",
        tiles:[["M1","M1","M1"],["M9","M9","M9"],["P1","P1","P1"],["P9","P9","P9"],["S9","S9"]] },
      { name:"混么九", cls:"yr-special", desc:"所有牌為么九牌＋字牌",
        tiles:[["M1","M1","M1"],["M9","M9","M9"],["Z1","Z1","Z1"],["Z5","Z5","Z5"],["P9","P9"]] },
    ]
  },
  {
    title: "🏆 豪華役",
    items: [
      { name:"大三元", cls:"yr-special", desc:"中・發・白 各刻三張",
        tiles:[["Z5","Z5","Z5"],["Z6","Z6","Z6"],["Z7","Z7","Z7"],["M1","M2","M3"],["P1","P1"]] },
      { name:"小三元", cls:"",           desc:"中・發・白 兩刻＋一對",
        tiles:[["Z5","Z5","Z5"],["Z6","Z6","Z6"],["M1","M2","M3"],["P1","P1","P1"],["Z7","Z7"]] },
      { name:"大四喜", cls:"yr-special", desc:"東南西北 各刻三張",
        tiles:[["Z1","Z1","Z1"],["Z2","Z2","Z2"],["Z3","Z3","Z3"],["Z4","Z4","Z4"],["M1","M1"]] },
      { name:"小四喜", cls:"",           desc:"東南西北 三刻＋一對",
        tiles:[["Z1","Z1","Z1"],["Z2","Z2","Z2"],["Z3","Z3","Z3"],["M1","M2","M3"],["Z4","Z4"]] },
      { name:"四暗刻", cls:"yr-special", desc:"手中4組暗刻（未碰出的刻子）",
        tiles:[["M1","M1","M1"],["P5","P5","P5"],["S3","S3","S3"],["M9","M9","M9"],["Z1","Z1"]] },
      { name:"三暗刻", cls:"",           desc:"手中3組暗刻",
        tiles:[["M1","M1","M1"],["P5","P5","P5"],["S3","S3","S3"],["M2","M3","M4"],["Z1","Z1"]] },
    ]
  },
  {
    title: "🔗 複合役",
    items: [
      { name:"一氣通貫",cls:"", desc:"同花色 123、456、789 各一組",
        tiles:[["M1","M2","M3"],["M4","M5","M6"],["M7","M8","M9"],["P2","P3","P4"],["S1","S1"]] },
      { name:"三色同順",cls:"", desc:"萬・筒・條 相同起點順子各一組",
        tiles:[["M2","M3","M4"],["P2","P3","P4"],["S2","S3","S4"],["M7","M7","M7"],["Z1","Z1"]] },
      { name:"三色同刻",cls:"", desc:"萬・筒・條 相同數字刻子各一組",
        tiles:[["M5","M5","M5"],["P5","P5","P5"],["S5","S5","S5"],["M2","M3","M4"],["Z1","Z1"]] },
      { name:"一色三順",cls:"", desc:"同花色同起點順子三組",
        tiles:[["M1","M2","M3"],["M1","M2","M3"],["M1","M2","M3"],["M4","M5","M6"],["M7","M7"]] },
    ]
  },
  {
    title: "🃏 飛牌（萬用牌）規則",
    items: [
      { name:"飛可碰/吃",cls:"yr-fei", desc:"飛牌可作為萬用牌用於碰牌和吃牌",
        tiles:[["H1","M5","M5"]] },
      { name:"飛不可槓", cls:"yr-fei", desc:"飛牌不能用於槓牌操作",
        tiles:[["H1"]] },
      { name:"換回飛",   cls:"yr-fei", desc:"若摸到飛牌替代的那張牌，可換回飛牌",
        tiles:[["H1","M5"]] },
    ]
  },
  {
    title: "👥 三人麻將特別規則",
    items: [
      { name:"三人對局",    cls:"yr-special", desc:"東・南・西 三家對局，無北家位置",
        tiles:[["Z1","Z2","Z3"]] },
      { name:"牌山精簡",    cls:"",           desc:"無萬子(M)・無條子(S)・無北風(Z4)・無琴棋書畫(F9-F12)，共 76 張",
        tiles:[["P1","P5","P9"],["Z1","Z2","Z3"],["F1","F5","F13"]] },
      { name:"無吃牌",      cls:"",           desc:"三人麻將禁止吃牌（吃），僅可碰、槓、胡",
        tiles:[] },
      { name:"自摸加倍",    cls:"yr-special", desc:"自摸時，兩家各賠全額（非平分）",
        tiles:[] },
      { name:"榮胡只賠一家",cls:"",           desc:"榮胡時僅打牌者賠付，另一家不賠",
        tiles:[] },
      { name:"座位花（三人）",cls:"",         desc:"座位花只設東・南・西（F1對應東，F2對應南，F3對應西）",
        tiles:[["F1","F2","F3","F5","F6","F7"]] },
      { name:"碰中",        cls:"",           desc:"碰紅中 +1番",
        tiles:[["Z5","Z5","Z5"]] },
      { name:"碰發",        cls:"",           desc:"碰發財 +1番",
        tiles:[["Z6","Z6","Z6"]] },
      { name:"碰白",        cls:"",           desc:"碰白板 +1番",
        tiles:[["Z7","Z7","Z7"]] },
      { name:"大三元",      cls:"yr-special", desc:"中・發・白 各刻三張，+5番",
        tiles:[["Z5","Z5","Z5"],["Z6","Z6","Z6"],["Z7","Z7","Z7"],["P1","P2","P3"],["P5","P5"]] },
    ]
  },
];

function buildYakuRules() {
  const body = document.getElementById("yaku-rules-body");
  if (body.dataset.built) return; // 已建立過，不重複
  body.dataset.built = "1";

  YAKU_SECTIONS.forEach(({ title, items }) => {
    const sec = document.createElement("div");
    sec.className = "yr-section";

    const t = document.createElement("div");
    t.className = "yr-section-title";
    t.textContent = title;
    sec.appendChild(t);

    const grid = document.createElement("div");
    grid.className = "yr-grid";

    items.forEach(({ name, cls, desc, tiles }) => {
      const card = document.createElement("div");
      card.className = "yr-card" + (cls ? " " + cls : "");

      // 名稱 + 說明
      const hdr = document.createElement("div");
      hdr.className = "yr-header";
      const nm = document.createElement("span");
      nm.className = "yr-name";
      nm.textContent = name;
      hdr.appendChild(nm);

      const fan = YAKU_FAN[name];
      if (fan !== undefined && fan > 0) {
        const fb = document.createElement("span");
        fb.className = "yr-fan-badge";
        fb.textContent = `${fan}番`;
        hdr.appendChild(fb);
      }

      const ds = document.createElement("span");
      ds.className = "yr-desc";
      ds.textContent = desc;
      hdr.appendChild(ds);
      card.appendChild(hdr);

      // 牌例（若有）
      if (tiles.length > 0) {
        const tileRow = document.createElement("div");
        tileRow.className = "yr-tiles";
        tiles.forEach(group => {
          const meld = document.createElement("div");
          meld.className = "yr-meld";
          group.forEach(code => {
            meld.appendChild(renderTile(code, false));
          });
          tileRow.appendChild(meld);
        });
        card.appendChild(tileRow);
      }

      grid.appendChild(card);
    });

    sec.appendChild(grid);
    body.appendChild(sec);
  });
}

// ── 各役種番數（賠率）表 ─────────────────────────────────────────
const YAKU_FAN = {
  "天胡":     8,
  "地胡":     8,
  "嶺上開花": 1,
  "自摸":     1,
  "榮胡":     0,  // 榮胡本身不計番，由其他役計
  "清一色":   4,
  "混一色":   2,
  "字一色":   6,
  "門前清":   1,
  "斷幺":     1,
  "全帶幺":   2,
  "純全帶幺": 3,
  "全求人":   1,
  "七對":     2,
  "十三幺":   8,
  "清么九":   8,
  "混么九":   4,
  "碰碰胡":   2,
  "三暗刻":   2,
  "四暗刻":   8,
  "大三元":   8,
  "小三元":   4,
  "大四喜":   8,
  "小四喜":   4,
  "一氣通貫": 2,
  "三色同順": 2,
  "三色同刻": 2,
  "一色三順": 3,
  "平胡":     1,
  "花牌":     1,  // 每朵花 1 番（實際按數量累加）
  "飛牌":     1,  // 每張飛 1 番（實際按數量累加）
  // 三人麻將專屬
  "三人對局":     0,
  "無北風牌":     0,
  "無吃牌":       0,
  "自摸加倍":     0,
  "榮胡只賠一家": 0,
  "座位花（三人）":1,
  "碰中":         1,
  "碰發":         1,
  "碰白":         1,
};

// ── 役種名稱 → 詳細資訊查找表（從 YAKU_SECTIONS 建立）──────────
const YAKU_INFO_MAP = (() => {
  const map = {};
  YAKU_SECTIONS.forEach(({ items }) => {
    items.forEach(item => { map[item.name] = item; });
  });
  return map;
})();

function showYakuInfoPopup(name) {
  const info = YAKU_INFO_MAP[name];
  const popup = document.getElementById("yaku-info-popup");
  const nameEl = document.getElementById("yaku-info-name");
  const descEl = document.getElementById("yaku-info-desc");
  const tilesEl = document.getElementById("yaku-info-tiles");

  nameEl.textContent = name;
  nameEl.className = "yaku-info-name" +
    (info && info.cls && info.cls.includes("special") ? " is-special" :
     info && info.cls && info.cls.includes("flush")   ? " is-flush"   : "");
  descEl.textContent = info ? info.desc : "";
  tilesEl.innerHTML = "";

  if (info && info.tiles && info.tiles.length > 0) {
    info.tiles.forEach(group => {
      const meld = document.createElement("div");
      meld.className = "yaku-info-meld";
      group.forEach(code => meld.appendChild(renderTile(code, false)));
      tilesEl.appendChild(meld);
    });
  }

  popup.classList.remove("hidden");
}

// 顯示自訂牌面彈窗（用於花牌/飛牌等動態標籤）
function showTilesPopup(label, desc, tileCodes) {
  const popup  = document.getElementById("yaku-info-popup");
  const nameEl = document.getElementById("yaku-info-name");
  const descEl = document.getElementById("yaku-info-desc");
  const tilesEl = document.getElementById("yaku-info-tiles");

  nameEl.textContent = label;
  nameEl.className = "yaku-info-name";
  descEl.textContent = desc || "";
  tilesEl.innerHTML = "";

  if (tileCodes && tileCodes.length > 0) {
    const meld = document.createElement("div");
    meld.className = "yaku-info-meld";
    tileCodes.forEach(code => meld.appendChild(renderTile(code, false)));
    tilesEl.appendChild(meld);
  }

  popup.classList.remove("hidden");
}

document.getElementById("btn-yaku-info-close").addEventListener("click", () => {
  document.getElementById("yaku-info-popup").classList.add("hidden");
});
document.getElementById("yaku-info-popup").addEventListener("click", (e) => {
  if (e.target === e.currentTarget)
    e.currentTarget.classList.add("hidden");
});

document.getElementById("btn-yaku-rules").addEventListener("click", () => {
  buildYakuRules();
  document.getElementById("yaku-rules-overlay").style.display = "flex";
});
document.getElementById("btn-yaku-rules-close").addEventListener("click", () => {
  document.getElementById("yaku-rules-overlay").style.display = "none";
});

// 右上角遊戲菜單
(function () {
  const menuBtn      = document.getElementById("btn-game-menu");
  const dropdown     = document.getElementById("game-menu-dropdown");
  const yakuBtn      = document.getElementById("btn-game-yaku-rules");
  const tileRefBtn   = document.getElementById("btn-game-tile-ref");
  const kbdBtn       = document.getElementById("btn-game-kbd");

  function toggleMenu(e) {
    e.stopPropagation();
    dropdown.classList.toggle("hidden");
  }

  function closeMenu() {
    dropdown.classList.add("hidden");
  }

  if (menuBtn) menuBtn.addEventListener("click", toggleMenu);

  if (yakuBtn) yakuBtn.addEventListener("click", () => {
    closeMenu();
    buildYakuRules();
    document.getElementById("yaku-rules-overlay").style.display = "flex";
  });

  if (tileRefBtn) tileRefBtn.addEventListener("click", () => {
    closeMenu();
    showTileRefOverlay();
  });

  if (kbdBtn) kbdBtn.addEventListener("click", () => {
    closeMenu();
    showKbdOverlay();
  });

  document.addEventListener("click", () => closeMenu());
})();
document.getElementById("yaku-rules-overlay").addEventListener("click", (e) => {
  if (e.target === e.currentTarget) e.currentTarget.style.display = "none";
});

function showTileRefOverlay() {
  const body = document.getElementById("tile-ref-body");
  body.innerHTML = "";

  // 三人麻將牌型：無萬子、無條子、無北風、無琴棋書畫(F9-F12)
  const GROUPS = [
    {
      label: "筒子 P1–P9（三人版唯一數牌）",
      tiles: Array.from({ length: 9 }, (_, i) => `P${i + 1}`),
    },
    {
      label: "字牌　東 南 西 中 發 白（無北風）",
      tiles: ["Z1","Z2","Z3","Z5","Z6","Z7"],
    },
    {
      label: "花牌 F1–F8　春夏秋冬 梅蘭竹菊",
      tiles: [1,2,3,4,5,6,7,8].map(i => `F${i}`),
    },
    {
      label: "動物花 F13–F16　貓雞蟲鼠",
      tiles: [13,14,15,16].map(i => `F${i}`),
    },
    {
      label: "飛牌（萬用牌）H1–H4",
      tiles: ["H1", "H2", "H3", "H4"],
    },
  ];

  GROUPS.forEach(({ label, tiles }) => {
    const group = document.createElement("div");
    group.className = "tile-ref-group";

    const lbl = document.createElement("div");
    lbl.className = "tile-ref-label";
    lbl.textContent = label;
    group.appendChild(lbl);

    const row = document.createElement("div");
    row.className = "tile-ref-row";
    tiles.forEach(code => {
      row.appendChild(renderTile(code, true));
    });
    group.appendChild(row);
    body.appendChild(group);
  });

  document.getElementById("tile-ref-overlay").style.display = "flex";
}

// 胡牌畫面：只關閉面板，保留當前局
document.getElementById("btn-win-dismiss").addEventListener("click", () => {
  document.getElementById("win-overlay").classList.add("hidden");
});

// 胡牌記錄
function renderWinHistory() {
  const list = document.getElementById("win-history-list");
  if (!list) return;
  list.innerHTML = "";
  if (winHistory.length === 0) {
    const empty = document.createElement("div");
    empty.className = "win-history-empty";
    empty.textContent = "沒有記錄";
    list.appendChild(empty);
    return;
  }
  winHistory.forEach((r, i) => {
    const item = document.createElement("div");
    item.className = "win-history-item" + (r.snapshot ? " whr-clickable" : "");
    item.innerHTML = `
      <div class="whr-index">#${winHistory.length - i}</div>
      <div class="whr-time">${r.time}</div>
      <div class="whr-winner">
        <span class="whr-avatar">${r.avatar}</span>
        <span class="whr-name">${r.winner}</span>
        <span class="whr-type ${r.isDealer ? 'whr-dealer' : ''}">${r.winType}${r.isDealer ? '・庄' : ''}</span>
      </div>
      <div class="whr-score">
        <span class="whr-fan">${r.fan} 番</span>
        <span class="whr-payout whr-payout-pos">+${r.payout.toLocaleString()}</span>
        ${r.snapshot ? '<span class="whr-detail-hint">查看詳情 ›</span>' : ''}
      </div>`;
    if (r.snapshot) {
      item.addEventListener("click", () => openWinDetail(r));
    }
    list.appendChild(item);
  });
}

function openWinDetail(r) {
  const body = document.getElementById("win-detail-body");
  if (!body || !r.snapshot) return;
  const s = r.snapshot;
  body.innerHTML = `
    <div class="win-title">胡啦！</div>
    <div class="win-player-name">${s.name}</div>
    <div class="win-type">${s.type}</div>
    <div class="win-yaku">${s.yaku}</div>
    <div class="win-score">${s.score}</div>
    <div class="win-all-hands">${s.hands}</div>`;
  document.getElementById("win-detail-modal").classList.remove("hidden");
}

document.getElementById("btn-close-win-detail").addEventListener("click", () => {
  document.getElementById("win-detail-modal").classList.add("hidden");
});
document.getElementById("win-detail-modal").addEventListener("click", e => {
  if (e.target.classList.contains("win-detail-backdrop")) {
    document.getElementById("win-detail-modal").classList.add("hidden");
  }
});

document.getElementById("btn-show-win").addEventListener("click", () => {
  renderWinHistory();
  document.getElementById("win-history-modal").classList.remove("hidden");
});
document.getElementById("btn-close-win-history").addEventListener("click", () => {
  document.getElementById("win-history-modal").classList.add("hidden");
});
document.getElementById("win-history-modal").addEventListener("click", e => {
  if (e.target.classList.contains("win-history-backdrop")) {
    document.getElementById("win-history-modal").classList.add("hidden");
  }
});

// 胡牌畫面退出回主頁
document.getElementById("btn-win-exit").addEventListener("click", () => {
  document.getElementById("win-overlay").classList.add("hidden");
  resetState();
  resetScores(); // C：回主頁自動重置余額
  gameOver = true;
  render();
  document.getElementById("action-bar").style.display = "none";
  document.getElementById("home-screen").classList.remove("hidden");
  hideTopBar();
  refreshProfileCard();
});

// 骰子界面退出回主頁
document.getElementById("btn-dice-exit").addEventListener("click", () => {
  document.getElementById("dice-overlay").classList.add("hidden");
  document.getElementById("home-screen").classList.remove("hidden");
  hideTopBar();
  refreshProfileCard();
});

// 退出回主頁
document.getElementById("btn-exit").addEventListener("click", () => {
  resetState();
  resetScores(); // C：回主頁自動重置余額
  gameOver = true;
  render();
  document.getElementById("win-overlay").classList.add("hidden");
  document.getElementById("dice-overlay").classList.add("hidden");
  // 三人版：無吃牌選擇框（chi-select-overlay 不存在，安全跳過）
  const _cso = document.getElementById("chi-select-overlay");
  if (_cso) _cso.classList.add("hidden");
  document.getElementById("action-bar").style.display = "none";
  document.getElementById("home-screen").classList.remove("hidden");
  hideTopBar();
  refreshProfileCard();
});

function showActionOverlay(text) {
  const overlay = document.getElementById("action-overlay");
  const actionText = document.getElementById("action-text");
  if (!overlay || !actionText) return;
  actionText.textContent = text;
  overlay.classList.remove("hidden");
  overlay.style.animation = "none";
  overlay.offsetHeight;
  overlay.style.animation = "";
  setTimeout(() => {
    overlay.classList.add("hidden");
  }, 1200);
  if (!allMuted) {
    // 碰/吃/槓：TTS 語音播報
    if (window.speechSynthesis) {
      const actionMap = { "碰": "碰", "吃": "吃", "槓": "槓", "胡": "胡啦" };
      const spoken = actionMap[text];
      if (spoken) {
        setTimeout(() => {
          if (allMuted) return;
          const utt = new SpeechSynthesisUtterance(spoken);
          utt.lang = "zh-TW";
          utt.rate = 1.0;
          window.speechSynthesis.cancel();
          window.speechSynthesis.speak(utt);
        }, 600);
      }
    }
    // 胡：Web Audio 短促慶祝音（在大字彈出時立即響）
    if (text === "胡") {
      try {
        const ctx = new (window.AudioContext || window.webkitAudioContext)();
        // 快速上升三音：C5 → G5 → C6
        [[523.25, 0, 0.18], [783.99, 0.14, 0.22], [1046.5, 0.28, 0.4]].forEach(([freq, start, dur]) => {
          const osc = ctx.createOscillator();
          const gain = ctx.createGain();
          osc.connect(gain); gain.connect(ctx.destination);
          osc.type = "triangle";
          osc.frequency.value = freq;
          const t = ctx.currentTime + start;
          gain.gain.setValueAtTime(0, t);
          gain.gain.linearRampToValueAtTime(0.55, t + 0.015);
          gain.gain.exponentialRampToValueAtTime(0.001, t + dur);
          osc.start(t); osc.stop(t + dur + 0.02);
        });
      } catch (_) {}
    }
  }
}

// ── 胡牌手牌分解（將飛顯示在實際代替的位置）──────────────────────
// 傳入手牌陣列，回傳 [[pair], [meld1], [meld2], ...] 或 null
function decomposeWinningHand(tiles) {
  const raw  = tiles.filter(t => t[0] !== "H");
  const feis = tiles.filter(t => t[0] === "H");
  const counts = {};
  for (const t of raw) counts[t] = (counts[t] || 0) + 1;

  // 嘗試每種將牌組合（真實牌對、真實牌+飛、飛+飛）
  for (const key of sortedKeys(counts)) {
    if (counts[key] >= 2) {
      const r = solveHandMelds({...counts, [key]: counts[key] - 2}, feis.slice(), [[key, key]]);
      if (r) return r;
    }
    if (counts[key] >= 1 && feis.length >= 1) {
      const r = solveHandMelds({...counts, [key]: counts[key] - 1}, feis.slice(1), [[key, feis[0]]]);
      if (r) return r;
    }
  }
  if (feis.length >= 2) {
    const r = solveHandMelds({...counts}, feis.slice(2), [[feis[0], feis[1]]]);
    if (r) return r;
  }
  return null;
}

function sortedKeys(counts) {
  const order = { M: 0, P: 1, S: 2, Z: 3 };
  return Object.keys(counts).filter(k => counts[k] > 0).sort((a, b) => {
    const sa = order[a[0]] ?? 4, sb = order[b[0]] ?? 4;
    if (sa !== sb) return sa - sb;
    return parseInt(a.slice(1)) - parseInt(b.slice(1));
  });
}

function solveHandMelds(counts, feis, groups) {
  const keys = sortedKeys(counts);

  if (keys.length === 0) {
    if (feis.length === 0) return groups;
    if (feis.length % 3 === 0) {
      const r = [...groups];
      for (let i = 0; i < feis.length; i += 3) r.push(feis.slice(i, i + 3));
      return r;
    }
    return null;
  }

  const firstKey = keys[0];
  const suit = firstKey[0];
  const v = parseInt(firstKey.slice(1));

  // 嘗試刻子（3實牌、2實+1飛、1實+2飛）
  for (let f = 0; f <= Math.min(2, feis.length); f++) {
    const real = 3 - f;
    if ((counts[firstKey] || 0) >= real) {
      const c = {...counts, [firstKey]: counts[firstKey] - real};
      const meld = [...Array(real).fill(firstKey), ...feis.slice(0, f)];
      const r = solveHandMelds(c, feis.slice(f), [...groups, meld]);
      if (r) return r;
    }
  }

  // 嘗試順子（數牌）：firstKey 可在序列的第 0、1、2 位
  if (suit !== "Z") {
    for (let pos = 0; pos <= 2; pos++) {
      const base = v - pos;
      if (base < 1 || base + 2 > 9) continue;

      let ok = true;
      let feisLeft = feis.slice();
      const newCounts = {...counts, [firstKey]: counts[firstKey] - 1};
      const meldTiles = new Array(3);
      meldTiles[pos] = firstKey;

      for (let i = 0; i < 3 && ok; i++) {
        if (i === pos) continue;
        const tk = `${suit}${base + i}`;
        if ((newCounts[tk] || 0) > 0) {
          meldTiles[i] = tk;
          newCounts[tk]--;
        } else if (feisLeft.length > 0) {
          meldTiles[i] = feisLeft.shift();
        } else {
          ok = false;
        }
      }

      if (ok) {
        const r = solveHandMelds(newCounts, feisLeft, [...groups, meldTiles]);
        if (r) return r;
      }
    }
  }

  return null;
}

// ── 胡牌役種判斷 ───────────────────────────────────────────────
// handTiles: 剩餘手牌（含飛），openMelds: 副露陣列，decomposedGroups: 分解後分組
function classifyWinningHand(handTiles, openMelds, decomposedGroups, ctx = {}) {
  const { isRonghu = false, afterKong = false, isFirstTurn = false } = ctx;
  const isZimo = !isRonghu;
  const yaku = [];

  const allGroups = [
    ...openMelds.map(m => ({ tiles: m.tiles, mType: m.type })),
    ...(decomposedGroups || []).map(g => ({ tiles: g, mType: g.length === 2 ? "pair" : "hand" })),
  ];

  // 所有實牌（排除飛/花）
  const allReal = [
    ...openMelds.flatMap(m => m.tiles),
    ...(handTiles || []),
  ].filter(t => t[0] !== "H" && t[0] !== "F");

  const numSuitsSet = new Set(allReal.filter(t => t[0] !== "Z").map(t => t[0]));
  const hasZ = allReal.some(t => t[0] === "Z");
  const numSuits = [...numSuitsSet];
  const hasFullDecomp = decomposedGroups !== null && decomposedGroups !== undefined;

  // ── 特殊胡法 ────────────────────────────────────────────────────
  // 天胡（庄家第一摸即胡）
  if (isZimo && isFirstTurn && openMelds.length === 0)
    yaku.push({ name: "天胡", cls: "yaku-special" });
  // 地胡（閒家第一輪摸牌即胡）
  else if (isZimo && isFirstTurn && openMelds.length === 0)
    yaku.push({ name: "地胡", cls: "yaku-special" });

  // 嶺上開花（槓後補牌胡）
  if (afterKong)
    yaku.push({ name: "嶺上開花", cls: "yaku-special" });

  // 自摸 / 榮胡
  if (isZimo && !afterKong) yaku.push({ name: "自摸", cls: "" });
  if (isRonghu) yaku.push({ name: "榮胡", cls: "" });

  // ── 花色役 ──────────────────────────────────────────────────────
  if (numSuits.length === 1 && !hasZ)
    yaku.push({ name: "清一色", cls: "yaku-flush" });
  else if (numSuits.length === 1 && hasZ)
    yaku.push({ name: "混一色", cls: "" });
  else if (numSuits.length === 0 && hasZ)
    yaku.push({ name: "字一色", cls: "yaku-special" });

  // ── 門前清 ──────────────────────────────────────────────────────
  if (openMelds.length === 0) yaku.push({ name: "門前清", cls: "" });

  // ── 斷幺（手牌全為 2-8，無么九及字牌）────────────────────────
  const allSimples = allReal.every(t => {
    if (t[0] === "Z") return false;
    const v = parseInt(t.slice(1));
    return v >= 2 && v <= 8;
  });
  if (allSimples) yaku.push({ name: "斷幺", cls: "" });

  // ── 七對（無副露）───────────────────────────────────────────────
  if (openMelds.length === 0 && handTiles) {
    const raw7 = handTiles.filter(t => t[0] !== "H" && t[0] !== "F");
    const fei7 = handTiles.filter(t => t[0] === "H").length;
    const c7 = {};
    for (const t of raw7) c7[t] = (c7[t] || 0) + 1;
    const pairs7 = Object.values(c7).reduce((s, v) => s + Math.floor(v / 2), 0);
    const odds7  = Object.values(c7).filter(v => v % 2 === 1).length;
    if (pairs7 + Math.floor(fei7 / 2) >= 7 && odds7 <= fei7)
      yaku.push({ name: "七對", cls: "yaku-special" });
  }

  // ── 十三幺（無副露）─────────────────────────────────────────────
  // 三人版：無萬子/條子/北風，孤張只剩 P1,P9,Z1,Z2,Z3,Z5,Z6,Z7（8張）
  // 十三幺需 13 張不同孤張，三人版牌山不具備此條件，故不判定。
  // （保留此處僅作說明，永遠不會觸發）

  // ── 全帶幺（每組面子/將牌含么九或字牌）─────────────────────────
  if (hasFullDecomp) {
    const terminals = ["M1","M9","P1","P9","S1","S9"];
    const isTermOrHonor = t => terminals.includes(t) || t[0] === "Z";
    const allGroupsHaveTerm = allGroups.every(g =>
      g.tiles.some(t => t[0] !== "H" && isTermOrHonor(t))
    );
    if (allGroupsHaveTerm && !allSimples) {
      const pureOutside = allGroups.every(g =>
        g.tiles.some(t => t[0] !== "H" && terminals.includes(t))
      );
      if (pureOutside && !hasZ)
        yaku.push({ name: "純全帶幺", cls: "" });
      else
        yaku.push({ name: "全帶幺", cls: "" });
    }
  }

  // ── 碰碰胡（所有面子均為刻子）──────────────────────────────────
  const meldGroups = allGroups.filter(g => g.mType !== "pair" && g.tiles.length === 3);
  const allTriplets = hasFullDecomp && meldGroups.length > 0 && meldGroups.every(g => {
    const real = g.tiles.filter(t => t[0] !== "H");
    return real.length === 0 || new Set(real).size === 1;
  });
  if (allTriplets) yaku.push({ name: "碰碰胡", cls: "" });

  // ── 三暗刻 / 四暗刻（手牌中的暗刻）─────────────────────────────
  if (hasFullDecomp) {
    const openPengTiles = new Set(
      openMelds.filter(m => m.type === "peng" || m.type === "gang")
               .flatMap(m => m.tiles.filter(t => t[0] !== "H"))
    );
    const concealedTrips = (decomposedGroups || []).filter(g => {
      if (g.length !== 3) return false;
      const real = g.filter(t => t[0] !== "H");
      return real.length >= 2 && new Set(real).size === 1 && !openPengTiles.has(real[0]);
    });
    if (concealedTrips.length === 4) yaku.push({ name: "四暗刻", cls: "yaku-special" });
    else if (concealedTrips.length === 3) yaku.push({ name: "三暗刻", cls: "" });
  }

  // ── 平胡（全順子，將牌非字牌）──────────────────────────────────
  if (!allTriplets && hasFullDecomp) {
    const openAllSeq = openMelds.every(m => m.type === "chi");
    const handMelds = (decomposedGroups || []).filter(g => g.length === 3);
    const handAllSeq = handMelds.every(g => {
      const real = g.filter(t => t[0] !== "H");
      return real.length < 3 || new Set(real).size > 1;
    });
    const pair = (decomposedGroups || []).find(g => g.length === 2) || [];
    const pairReal = pair.filter ? pair.filter(t => t[0] !== "H") : [];
    if (openAllSeq && handAllSeq && (pairReal.length === 0 || pairReal[0][0] !== "Z"))
      yaku.push({ name: "平胡", cls: "" });
  }

  // ── 一氣通貫（同花色 123、456、789）────────────────────────────
  if (hasFullDecomp) {
    const seqByStartSuit = { M: new Set(), P: new Set(), S: new Set() };
    allGroups.forEach(g => {
      if (g.tiles.length !== 3) return;
      const real = g.tiles.filter(t => t[0] !== "H");
      if (real.length === 3 && new Set(real.map(t=>t[0])).size === 1 && ["M","P","S"].includes(real[0][0])) {
        const sorted = real.map(t => parseInt(t.slice(1))).sort((a,b)=>a-b);
        if (sorted[1] === sorted[0]+1 && sorted[2] === sorted[0]+2)
          seqByStartSuit[real[0][0]].add(sorted[0]);
      }
    });
    for (const s of ["M","P","S"]) {
      if (seqByStartSuit[s].has(1) && seqByStartSuit[s].has(4) && seqByStartSuit[s].has(7))
        yaku.push({ name: "一氣通貫", cls: "" });
    }
  }

  // ── 一色三順（同花色三組相同順子）──────────────────────────────
  if (hasFullDecomp) {
    const seqCount = {};
    allGroups.forEach(g => {
      if (g.tiles.length !== 3) return;
      const real = g.tiles.filter(t => t[0] !== "H");
      if (real.length === 3 && new Set(real).size > 1) {
        const sorted = real.map(t => parseInt(t.slice(1))).sort((a,b)=>a-b);
        if (sorted[1] === sorted[0]+1 && sorted[2] === sorted[0]+2) {
          const key = `${real[0][0]}${sorted[0]}`;
          seqCount[key] = (seqCount[key] || 0) + 1;
        }
      }
    });
    if (Object.values(seqCount).some(c => c >= 3)) yaku.push({ name: "一色三順", cls: "" });
  }

  // ── 大三元 / 小三元 ──────────────────────────────────────────────
  const dragons = ["Z5","Z6","Z7"];
  const dragonTrips = allGroups.filter(g => {
    if (g.mType === "pair" || g.tiles.length !== 3) return false;
    const real = g.tiles.filter(t => t[0] !== "H");
    return real.length >= 1 && dragons.includes(real[0]) && new Set(real).size === 1;
  });
  if (dragonTrips.length === 3) yaku.push({ name: "大三元", cls: "yaku-special" });
  else if (dragonTrips.length === 2) {
    const dragonPair = allGroups.some(g =>
      g.tiles.length === 2 && g.tiles.filter(t => t[0] !== "H").some(t => dragons.includes(t))
    );
    if (dragonPair) yaku.push({ name: "小三元", cls: "" });
  }

  // ── 大四喜 / 小四喜 ──────────────────────────────────────────────
  const winds = ["Z1","Z2","Z3","Z4"];
  const windTrips = allGroups.filter(g => {
    if (g.mType === "pair" || g.tiles.length !== 3) return false;
    const real = g.tiles.filter(t => t[0] !== "H");
    return real.length >= 1 && winds.includes(real[0]) && new Set(real).size === 1;
  });
  if (windTrips.length === 4) yaku.push({ name: "大四喜", cls: "yaku-special" });
  else if (windTrips.length === 3) {
    const windPair = allGroups.some(g =>
      g.tiles.length === 2 && g.tiles.filter(t => t[0] !== "H").some(t => winds.includes(t))
    );
    if (windPair) yaku.push({ name: "小四喜", cls: "" });
  }

  // ── 混么九 / 清么九（所有牌為么九牌）───────────────────────────
  const termList = ["M1","M9","P1","P9","S1","S9"];
  const allTermOrHonor = allReal.every(t => termList.includes(t) || t[0] === "Z");
  if (allTermOrHonor && numSuits.length > 0 && hasZ)
    yaku.push({ name: "混么九", cls: "yaku-special" });
  else if (allTermOrHonor && numSuits.length > 0 && !hasZ)
    yaku.push({ name: "清么九", cls: "yaku-special" });

  // ── 三色同刻 ────────────────────────────────────────────────────
  const tripValues = { M: new Set(), P: new Set(), S: new Set() };
  allGroups.forEach(g => {
    if (g.mType === "pair" || g.tiles.length !== 3) return;
    const real = g.tiles.filter(t => t[0] !== "H");
    if (real.length >= 1 && ["M","P","S"].includes(real[0][0]) && new Set(real).size === 1)
      tripValues[real[0][0]].add(real[0].slice(1));
  });
  const commonTrip = [...tripValues.M].find(v => tripValues.P.has(v) && tripValues.S.has(v));
  if (commonTrip) yaku.push({ name: "三色同刻", cls: "" });

  // ── 三色同順 ────────────────────────────────────────────────────
  if (hasFullDecomp) {
    const seqValues = { M: new Set(), P: new Set(), S: new Set() };
    allGroups.forEach(g => {
      if (g.tiles.length !== 3) return;
      const real = g.tiles.filter(t => t[0] !== "H");
      if (real.length === 3 && new Set(real).size > 1 && ["M","P","S"].includes(real[0][0])) {
        const sorted = real.map(t => parseInt(t.slice(1))).sort((a,b)=>a-b);
        if (sorted[1] === sorted[0]+1 && sorted[2] === sorted[0]+2)
          seqValues[real[0][0]].add(sorted[0]);
      }
    });
    const commonSeq = [...seqValues.M].find(v => seqValues.P.has(v) && seqValues.S.has(v));
    if (commonSeq) yaku.push({ name: "三色同順", cls: "" });
  }

  // ── 全求人（全部靠榮胡且無暗刻，不自摸）────────────────────────
  if (isRonghu && openMelds.length > 0 && openMelds.every(m => m.type !== "gang")) {
    const hasConcealed = hasFullDecomp && (decomposedGroups || []).some(g => {
      if (g.length !== 3) return false;
      const real = g.filter(t => t[0] !== "H");
      return real.length >= 2 && new Set(real).size === 1;
    });
    if (!hasConcealed) yaku.push({ name: "全求人", cls: "" });
  }

  // ── 普通胡（無特殊役，作為兜底顯示）────────────────────────────
  // 只在沒有其他有意義的役時顯示
  const meaningfulYaku = yaku.filter(y => !["自摸","榮胡","門前清"].includes(y.name));
  if (meaningfulYaku.length === 0) yaku.push({ name: "普通胡", cls: "yaku-normal" });

  return yaku;
}

// ─────────────────────────────────────────────────────────────────
// 聽牌分析：找出所有「丟哪張 → 等哪些牌」的方案
function findTenpaiOptions(hand) {
  const allTileTypes = [
    ...["M","P","S"].flatMap(s => Array.from({ length: 9 }, (_, i) => `${s}${i + 1}`)),
    ...Array.from({ length: 7 }, (_, i) => `Z${i + 1}`),
  ];

  // 統計場上已可見的每種牌數量（弃牌 + 副露 + 手牌本身）
  // 若某牌已有 4 張可見，牌山中不可能再摸到，不列為等牌
  const visibleCount = {};
  const allPlayers = [PLAYER_SOUTH, AI_EAST, AI_WEST]; // 三人版：無北家
  allPlayers.forEach(pid => {
    discards[pid].forEach(t => {
      if (t[0] !== "H" && t[0] !== "F") visibleCount[t] = (visibleCount[t] || 0) + 1;
    });
    (melds[pid] || []).forEach(m => {
      m.tiles.forEach(t => {
        if (t[0] !== "H" && t[0] !== "F") visibleCount[t] = (visibleCount[t] || 0) + 1;
      });
    });
  });
  hand.forEach(t => {
    if (t[0] !== "H" && t[0] !== "F") visibleCount[t] = (visibleCount[t] || 0) + 1;
  });

  const results = [];
  const seen = new Set();

  for (let i = 0; i < hand.length; i++) {
    const discardTile = hand[i];
    if (seen.has(discardTile)) continue;
    seen.add(discardTile);

    const remaining = [...hand.slice(0, i), ...hand.slice(i + 1)];
    // 手牌長度須為 (3n+1) 才能等一張成胡
    if ((remaining.length + 1) % 3 !== 2) continue;

    // 丟出這張後，重新計算可見數（手牌少一張）
    const countAfterDiscard = { ...visibleCount };
    if (discardTile[0] !== "H" && discardTile[0] !== "F") {
      countAfterDiscard[discardTile] = (countAfterDiscard[discardTile] || 0) - 1;
    }

    const winTiles = [];
    for (const t of allTileTypes) {
      // 若此牌 4 張已全部可見（牌山已無），不列為等牌
      if ((countAfterDiscard[t] || 0) >= 4) continue;
      if (MJ.isWinningHand([...remaining, t])) winTiles.push(t);
    }
    if (winTiles.length > 0) results.push({ discard: discardTile, winTiles });
  }

  // 等牌數多的排前面（越多等牌越靈活）
  results.sort((a, b) => b.winTiles.length - a.winTiles.length);
  return results;
}

function showTenpaiOverlay() {
  const overlay = document.getElementById("tenpai-overlay");
  if (!overlay) return;

  const hand = hands[PLAYER_SOUTH];
  const options = findTenpaiOptions(hand);
  const body = document.getElementById("tenpai-body");
  body.innerHTML = "";

  if (options.length === 0) {
    body.innerHTML = `<p class="tenpai-none">目前手牌尚未接近聽牌，繼續摸牌吧！</p>`;
  } else {
    options.forEach(({ discard, winTiles }) => {
      const row = document.createElement("div");
      row.className = "tenpai-row";

      // 丟出的牌
      const discardWrap = document.createElement("div");
      discardWrap.className = "tenpai-discard-wrap";
      const discardLabel = document.createElement("span");
      discardLabel.className = "tenpai-label";
      discardLabel.textContent = "丟出";
      const discardTileEl = renderTile(discard, ["player", "tenpai-tile"]);
      discardWrap.appendChild(discardLabel);
      discardWrap.appendChild(discardTileEl);

      // 箭頭
      const arrow = document.createElement("span");
      arrow.className = "tenpai-arrow";
      arrow.textContent = "→";

      // 等牌
      const waitWrap = document.createElement("div");
      waitWrap.className = "tenpai-wait-wrap";
      const waitLabel = document.createElement("span");
      waitLabel.className = "tenpai-label";
      waitLabel.textContent = `聽（${winTiles.length} 張）`;
      const waitTiles = document.createElement("div");
      waitTiles.className = "tenpai-wait-tiles";
      winTiles.forEach(t => {
        waitTiles.appendChild(renderTile(t, ["player", "tenpai-tile"]));
      });
      waitWrap.appendChild(waitLabel);
      waitWrap.appendChild(waitTiles);

      row.appendChild(discardWrap);
      row.appendChild(arrow);
      row.appendChild(waitWrap);
      body.appendChild(row);
    });
  }

  overlay.style.display = "flex";
}

// ── 計算並應用賠付 ────────────────────────────────────────────────
// 回傳 { deltas: { pid: amount }, winnerGain }，amount > 0 為贏得，< 0 為賠出
// fanReductions: { [pid]: reduceFan }  個別扣番（手中有飛對方）
// duifeiBonus  : 胡家手中有飛張數 → 三家各多賠 duifeiBonus 番（對飛）
// ── 三人麻將賠付規則：自摸→兩家各賠全額；榮胡→僅打牌者賠全額 ──
// 榮胡：僅打牌者賠 fan × BASE_UNIT × 2 × mult（兩家份額）；另家不賠
// 自摸：兩家各賠 fan × BASE_UNIT × mult（各賠全額）
function calculateAndApplyPayout(winner, totalFan, isRonghu, discardFrom, fanReductions = {}, duifeiBonus = 0) {
  const all = [PLAYER_SOUTH, AI_EAST, AI_WEST]; // 三人版：3位玩家
  const isDealer = winner === dealerPlayer;
  const mult = isDealer ? 2 : 1;
  const deltas = {};
  all.forEach(pid => { deltas[pid] = 0; });

  if (totalFan <= 0 && duifeiBonus <= 0 && Object.keys(fanReductions).length === 0)
    return { deltas, winnerGain: 0 };

  // 每位對家的有效番數（主番扣減對方飛牌）
  const effectiveFan = (pid) => Math.max(0, totalFan - (fanReductions[pid] || 0));
  // 對飛：對方手中每張飛牌可抵消 1 番對飛費
  const oppFeiCount = (pid) => (hands[pid] || []).filter(t => t[0] === "H").length;
  const duifeiPay = (pid) => Math.max(0, duifeiBonus - oppFeiCount(pid)) * BASE_UNIT * mult;

  let winnerGain = 0;
  if (isRonghu) {
    // 榮胡（三人版）：打牌者賠主番 × 2（兩家份額）；另家各賠對飛番
    const from = discardFrom ?? null;
    all.forEach(pid => {
      if (pid === winner) return;
      let pay = duifeiPay(pid);                          // 對飛：兩家各賠
      if (pid === from) pay += effectiveFan(from) * BASE_UNIT * 2 * mult; // 打牌者賠主番×2
      if (pay > 0) {
        deltas[pid]    -= pay;
        deltas[winner] += pay;
        winnerGain += pay;
      }
    });
  } else {
    // 自摸（三人版）：兩家各賠全額（主番 + 對飛番）
    all.forEach(pid => {
      if (pid === winner) return;
      const pay = effectiveFan(pid) * BASE_UNIT * mult + duifeiPay(pid);
      deltas[pid]    -= pay;
      deltas[winner] += pay;
      winnerGain += pay;
    });
  }

  // 套用到 scores
  all.forEach(pid => { scores[pid] += deltas[pid]; });
  return { deltas, winnerGain };
}

// ─────────────────────────────────────────────────────────────────
function showWinOverlay(winner, { winTile = null, isRonghu = false, afterKong = false } = {}) {
  const overlay  = document.getElementById("win-overlay");
  const nameEl   = document.getElementById("win-player-name");
  const typeEl   = document.getElementById("win-type");
  const yakuEl   = document.getElementById("win-yaku");
  const allHands = document.getElementById("win-all-hands");

  // 重置標題（防止流局後殘留「流局！」樣式）
  const titleEl = document.getElementById("win-title");
  if (titleEl) { titleEl.textContent = "胡啦！"; titleEl.classList.remove("draw"); }
  const closeBtn = document.getElementById("btn-close-win");
  if (closeBtn) closeBtn.textContent = "開始新局";

  // 各座位頭像對照（三人版：無北家）
  const SEAT_AVATAR = { S: playerAvatar, E: "🐯", W: "🦁" };

  nameEl.innerHTML = "";
  const avatarSpan = document.createElement("span");
  avatarSpan.className = "game-avatar win-avatar";
  avatarSpan.textContent = SEAT_AVATAR[winner] ?? "🀄";
  nameEl.appendChild(avatarSpan);
  const nameText = document.createTextNode(getSeatName(winner));
  nameEl.appendChild(nameText);
  if (winner === dealerPlayer) {
    const dealerBadge = document.createElement("span");
    dealerBadge.className = "win-dealer-badge";
    dealerBadge.textContent = "庄";
    nameEl.appendChild(dealerBadge);
  }
  typeEl.textContent = isRonghu
    ? `榮胡 ── 胡：${winTile ? formatTileLabel(winTile) : ""}`
    : "自摸";

  if (yakuEl) yakuEl.innerHTML = "";

  // ── 役種標籤（贏家手牌） ──────────────────────────────
  const displayHand = isRonghu && winTile
    ? [...hands[winner], winTile]
    : hands[winner].slice();
  const decomposed = decomposeWinningHand(displayHand);
  const isFirstTurn = turnCount <= 4; // 前4次摸牌（天胡/地胡範圍）
  const yakuList = classifyWinningHand(displayHand, melds[winner], decomposed, {
    isRonghu, afterKong, isFirstTurn
  });
  // 計算總番數
  let totalFan = 0;
  if (yakuEl && yakuList.length > 0) {
    yakuList.forEach(({ name, cls }) => {
      const fan = YAKU_FAN[name] ?? 0;
      totalFan += fan;
      const tag = document.createElement("span");
      tag.className = `yaku-tag ${cls || ""}`.trim();
      tag.title = "點擊查看牌型說明";
      tag.addEventListener("click", () => showYakuInfoPopup(name));
      tag.appendChild(document.createTextNode(name));
      if (fan > 0) {
        const badge = document.createElement("span");
        badge.className = "yaku-fan-badge";
        badge.textContent = `+${fan}番`;
        tag.appendChild(badge);
      }
      yakuEl.appendChild(tag);
    });
  }

  // ── 工具：新增役種 tag 並累加番數 ─────────────────────
  const addFanTag = (label, fan, cls = "", tiles = null) => {
    if (!yakuEl) return;
    const tag = document.createElement("span");
    tag.className = ("yaku-tag " + cls).trim();
    tag.appendChild(document.createTextNode(label));
    if (fan > 0) {
      totalFan += fan;
      const badge = document.createElement("span");
      badge.className = "yaku-fan-badge";
      badge.textContent = `+${fan}番`;
      tag.appendChild(badge);
    }
    if (tiles && tiles.length > 0) {
      tag.style.cursor = "pointer";
      tag.title = "點擊查看牌型";
      tag.addEventListener("click", () => showTilesPopup(label, "", tiles));
    }
    yakuEl.appendChild(tag);
  };

  // ── 風位動態計算（三人版：庄家=東風，出牌順序南→西→東）─
  // 三人版出牌順序：南 → 西 → 東（無北）
  const TURN_ORDER = [PLAYER_SOUTH, AI_WEST, AI_EAST];
  const dealerIdx  = TURN_ORDER.indexOf(dealerPlayer);
  const seatPos    = (p) => ((TURN_ORDER.indexOf(p) - dealerIdx + 3) % 3) + 1;
  // 三人版位置 1=東風(Z1) 2=南風(Z2) 3=西風(Z3)（無北風Z4）
  const WIND_TILES  = ["Z1", "Z2", "Z3"];
  const seatWindTile = WIND_TILES[seatPos(winner) - 1];
  const openWindTrip = (melds[winner] || []).some(m =>
    (m.type === "peng" || m.type === "gang") &&
    m.tiles.filter(t => t[0] !== "H").every(t => t === seatWindTile)
  );
  const handWindTrip = (decomposed || []).some(g =>
    g.length === 3 &&
    g.filter(t => t[0] !== "H").length >= 2 &&
    g.filter(t => t[0] !== "H").every(t => t === seatWindTile)
  );
  const windTripTiles = [seatWindTile, seatWindTile, seatWindTile];
  // 大四喜 / 小四喜 已包含所有風牌刻，不再另算自風刻
  const hasSixi = yakuList.some(y => y.name === "大四喜" || y.name === "小四喜");
  if (!hasSixi && (openWindTrip || handWindTrip)) addFanTag("自風刻", 1, "", windTripTiles);

  // ── 三元牌刻（碰中/發/白）各 1 番 ────────────────────
  // 大三元 / 小三元 已包含所有三元牌刻，不再另算碰中/發/白
  const hasSanyuan = yakuList.some(y => y.name === "大三元" || y.name === "小三元");
  if (!hasSanyuan) {
    const hasTriplet = (tile) =>
      (melds[winner] || []).some(m =>
        (m.type === "peng" || m.type === "gang") &&
        m.tiles.filter(t => t[0] !== "H").every(t => t === tile)
      ) ||
      (decomposed || []).some(g =>
        g.length === 3 &&
        g.filter(t => t[0] !== "H").length >= 2 &&
        g.filter(t => t[0] !== "H").every(t => t === tile)
      );
    const DRAGONS = [
      { tile: "Z5", name: "碰中" },
      { tile: "Z6", name: "碰發" },
      { tile: "Z7", name: "碰白" },
    ];
    DRAGONS.forEach(({ tile, name }) => {
      if (hasTriplet(tile)) addFanTag(name, 1, "", [tile, tile, tile]);
    });
  }


  // ── 花牌詳細番數 ─────────────────────────────────────
  const seatNum = seatPos(winner);  // 與風位相同，庄家=1
  const winnerFlowerTiles = flowers[winner] || [];
  const winnerFlowerNums  = winnerFlowerTiles.map(f => parseInt(f.slice(1)));

  // 座位花：三組各按座位號對應，各 1 番
  // ① 春夏秋冬 F1-F4  ② 梅蘭竹菊 F5-F8  ③ 琴棋書畫 F9-F12
  const seatF1Tiles = winnerFlowerTiles.filter(f => parseInt(f.slice(1)) === seatNum);
  const seatF2Tiles = winnerFlowerTiles.filter(f => parseInt(f.slice(1)) === seatNum + 4);
  const seatF3Tiles = winnerFlowerTiles.filter(f => parseInt(f.slice(1)) === seatNum + 8);
  if (seatF1Tiles.length > 0) addFanTag("座位花①", seatF1Tiles.length, "", seatF1Tiles);
  if (seatF2Tiles.length > 0) addFanTag("座位花②", seatF2Tiles.length, "", seatF2Tiles);
  if (seatF3Tiles.length > 0) addFanTag("座位花③", seatF3Tiles.length, "", seatF3Tiles);

  // 湊齊一組全：三人版只有 F1-F4、F5-F8（無琴棋書畫 F9-F12）
  const set1Tiles = [1,2,3,4].map(n => `F${n}`);
  const set2Tiles = [5,6,7,8].map(n => `F${n}`);
  if ([1,2,3,4].every(n => winnerFlowerNums.includes(n))) addFanTag("春夏秋冬全", 1, "", set1Tiles);
  if ([5,6,7,8].every(n => winnerFlowerNums.includes(n))) addFanTag("梅蘭竹菊全", 1, "", set2Tiles);
  // 三人版無琴棋書畫（F9-F12），不計此組

  // 動物花牌 F13–F16：每張 1 番
  const animalTiles = winnerFlowerTiles.filter(f => {
    const n = parseInt(f.slice(1)); return n >= 13 && n <= 16;
  });
  if (animalTiles.length > 0) addFanTag("動物花", animalTiles.length, "", animalTiles);

  // ── 飛牌（已換出）：每張 1 番 ─────────────────────────
  const winnerFeiTiles = feis[winner] || [];
  if (winnerFeiTiles.length > 0) addFanTag("飛牌", winnerFeiTiles.length, "", winnerFeiTiles);

  // ── 對飛：己方手中有飛，三家各多賠 1 番 ───────────────
  const feisInOwnHand = displayHand.filter(t => t[0] === "H");
  const duifeiBonus = feisInOwnHand.length;   // 每張飛對三家各 +1 番
  if (duifeiBonus > 0) {
    if (yakuEl) {
      const tag = document.createElement("span");
      tag.className = "yaku-tag";
      tag.style.cursor = "pointer";
      tag.title = "點擊查看牌型";
      tag.appendChild(document.createTextNode("對飛"));
      const badge = document.createElement("span");
      badge.className = "yaku-fan-badge";
      badge.textContent = `+${duifeiBonus}番/家`;
      tag.appendChild(badge);
      tag.addEventListener("click", () => showTilesPopup("對飛（手中飛牌）", `三家各多賠 ${duifeiBonus} 番`, feisInOwnHand));
      yakuEl.appendChild(tag);
    }
  }

  // 對飛番計入總番數顯示（賠付函數仍以原 totalFan 計算，duifeiBonus 單獨傳入）
  const baseFanForPayout = totalFan;
  totalFan += duifeiBonus;

  const fanReductions = {};

  // ── 計算賠付並更新分數 ──────────────────────────────────
  const discardFrom = isRonghu ? (lastDiscard?.from ?? null) : null;
  const { deltas } = calculateAndApplyPayout(winner, baseFanForPayout, isRonghu, discardFrom, fanReductions, duifeiBonus);
  const isDealer = winner === dealerPlayer;

  // ── 存入胡牌記錄 ──────────────────────────────────────────
  const _winnerName = winner === PLAYER_SOUTH ? (playerName || "玩家") : getSeatName(winner);
  const _payout     = deltas[winner] ?? 0;
  const _now        = new Date();
  const _pad        = n => String(n).padStart(2, "0");
  const _timeStr    = `${_now.getFullYear()}/${_pad(_now.getMonth()+1)}/${_pad(_now.getDate())} `
                    + `${_pad(_now.getHours())}:${_pad(_now.getMinutes())}`;
  winHistory.unshift({
    time:      _timeStr,
    winner:    _winnerName,
    avatar:    (winner === PLAYER_SOUTH ? playerAvatar : { E:"🐯", W:"🦁", N:"🤖" }[winner]) ?? "🀄",
    fan:       totalFan,
    payout:    _payout,
    winType:   isRonghu ? "榮胡" : "自摸",
    isDealer:  isDealer,
  });
  const mult = isDealer ? 2 : 1;

  // ── 破產檢測 ─────────────────────────────────────────────
  const bankruptPlayers = TURN_ORDER.filter(pid => scores[pid] <= 0);
  if (bankruptPlayers.length > 0) {
    sessionOver = true;
    const noticeEl = document.getElementById("bankrupt-notice");
    if (noticeEl) {
      const names = bankruptPlayers.map(getSeatName).join("、");
      noticeEl.textContent = `💸 ${names} 籌碼耗盡！本場遊戲結束，請退出重新開始。`;
      noticeEl.classList.remove("hidden");
    }
    const closeBtn = document.getElementById("btn-close-win");
    if (closeBtn) closeBtn.textContent = "退出到主页";
  }

  // ── 番數匯總 ────────────────────────────────────────────
  const scoreEl = document.getElementById("win-score");
  if (scoreEl) {
    scoreEl.innerHTML = "";
    if (totalFan > 0) {
      // 總番數大字
      const row = document.createElement("div");
      row.className = "win-score-row";
      const lbl = document.createElement("span");
      lbl.className = "win-score-label";
      lbl.textContent = "總番數";
      const total = document.createElement("span");
      total.className = "win-score-total";
      total.textContent = totalFan;
      const unit = document.createElement("span");
      unit.className = "win-score-unit";
      unit.textContent = "番";
      row.appendChild(lbl);
      row.appendChild(total);
      row.appendChild(unit);
      scoreEl.appendChild(row);

      // 實際賠付金額說明
      const singlePay = totalFan * BASE_UNIT * mult;
      const payEl = document.createElement("div");
      payEl.className = "win-score-payout";
      if (isRonghu) {
        payEl.innerHTML = `榮胡：打牌者賠 <strong>+${(singlePay * 2).toLocaleString()} 分</strong>${duifeiBonus > 0 ? `（另：兩家各賠對飛 ${(duifeiBonus * BASE_UNIT * mult).toLocaleString()} 分）` : ""}`;
      } else {
        payEl.innerHTML = `自摸：兩家各賠 <strong>${singlePay.toLocaleString()} 分</strong>（共 +${(singlePay * 2).toLocaleString()} 分）`;
      }
      scoreEl.appendChild(payEl);

      if (isDealer) {
        const dealerNote = document.createElement("span");
        dealerNote.className = "win-score-dealer";
        dealerNote.textContent = "庄家勝 × 2";
        scoreEl.appendChild(dealerNote);
      }
    }
  }

  // ── 全場牌型展示（三人版：南·東·西）────────────────────
  allHands.innerHTML = "";
  const DIR_LABEL = { S: "南", E: "東", W: "西" };
  const SEAT_ORDER = [PLAYER_SOUTH, AI_EAST, AI_WEST];

  SEAT_ORDER.forEach(pid => {
    const isWinner = pid === winner;
    const pidHand = isWinner ? displayHand : [...hands[pid]];
    const pidMelds = melds[pid] || [];

    const row = document.createElement("div");
    row.className = isWinner ? "wah-row wah-winner" : "wah-row";

    // 左側：玩家資訊列
    const info = document.createElement("div");
    info.className = "wah-info";

    const wahAvatar = document.createElement("span");
    wahAvatar.className = "game-avatar wah-avatar";
    wahAvatar.textContent = SEAT_AVATAR[pid] ?? "🀄";
    info.appendChild(wahAvatar);

    const dirBadge = document.createElement("span");
    dirBadge.className = "wah-dir";
    dirBadge.textContent = DIR_LABEL[pid] || "";
    info.appendChild(dirBadge);

    const nameSpan = document.createElement("span");
    nameSpan.className = "wah-name";
    nameSpan.textContent = pid === PLAYER_SOUTH ? playerName : getSeatName(pid).replace("人機 ", "AI");
    info.appendChild(nameSpan);

    if (isWinner) {
      const badge = document.createElement("span");
      badge.className = "wah-win-badge";
      badge.textContent = isRonghu ? "榮胡" : "自摸";
      info.appendChild(badge);
    }

    if (pid === dealerPlayer) {
      const db = document.createElement("span");
      db.className = "win-dealer-badge";
      db.textContent = "庄";
      info.appendChild(db);
    }

    // 分數變動 + 目前餘額
    const delta = deltas[pid] ?? 0;
    const scoreAfter = scores[pid];
    const scoreDiv = document.createElement("div");
    scoreDiv.className = "wah-score";
    const deltaSpan = document.createElement("span");
    deltaSpan.className = delta >= 0 ? "wah-delta wah-delta-pos" : "wah-delta wah-delta-neg";
    deltaSpan.textContent = (delta >= 0 ? "+" : "") + delta.toLocaleString();
    const balSpan = document.createElement("span");
    balSpan.className = "wah-balance";
    balSpan.textContent = scoreAfter.toLocaleString();
    scoreDiv.appendChild(deltaSpan);
    scoreDiv.appendChild(balSpan);
    info.appendChild(scoreDiv);
    row.appendChild(info);

    // 右側：副露 + 手牌
    const tilesWrap = document.createElement("div");
    tilesWrap.className = "wah-tiles";

    // 副露
    pidMelds.forEach(meld => {
      const grp = document.createElement("div");
      grp.className = "wah-meld-group";
      meld.tiles.forEach(t => grp.appendChild(renderTile(t, false)));
      tilesWrap.appendChild(grp);
    });

    // 手牌 — 贏家嘗試分組顯示，其他玩家排序顯示
    if (isWinner && decomposed) {
      let marked = false;
      decomposed.forEach(group => {
        const grpDiv = document.createElement("div");
        grpDiv.className = group.length === 2 ? "wah-meld-group wah-pair" : "wah-meld-group";
        group.forEach(t => {
          const tileEl = renderTile(t, false);
          if (isRonghu && !marked && t === winTile) {
            tileEl.classList.add("win-tile");
            marked = true;
          }
          grpDiv.appendChild(tileEl);
        });
        tilesWrap.appendChild(grpDiv);
      });
    } else {
      const sorted = MJ.sortHand(pidHand);
      const handGrp = document.createElement("div");
      handGrp.className = "wah-meld-group";
      let marked = false;
      sorted.forEach(t => {
        const tileEl = renderTile(t, false);
        if (isWinner && isRonghu && !marked && t === winTile) {
          tileEl.classList.add("win-tile");
          marked = true;
        }
        handGrp.appendChild(tileEl);
      });
      tilesWrap.appendChild(handGrp);
    }

    // 花牌（如有）
    const pidFlowers = flowers[pid] || [];
    if (pidFlowers.length > 0) {
      const sep = document.createElement("div");
      sep.className = "wah-sep";
      tilesWrap.appendChild(sep);
      pidFlowers.forEach(t => tilesWrap.appendChild(renderTile(t, false)));
    }

    row.appendChild(tilesWrap);
    allHands.appendChild(row);
  });

  overlay.classList.remove("hidden");

  // ── 胡牌發聲（Web Audio 勝利音效，無需音頻文件）──────────────
  if (!allMuted) {
    try {
      const ctx = new (window.AudioContext || window.webkitAudioContext)();
      const master = ctx.createGain();
      master.gain.value = 0.6;
      master.connect(ctx.destination);

      // 上升琶音：C5→E5→G5→C6，加混響感
      const notes = [
        [523.25, 0.00, 0.35],
        [659.25, 0.12, 0.35],
        [783.99, 0.24, 0.35],
        [1046.5, 0.38, 0.55],
      ];
      notes.forEach(([freq, start, dur]) => {
        const osc  = ctx.createOscillator();
        const gain = ctx.createGain();
        osc.connect(gain);
        gain.connect(master);
        osc.type = "triangle";
        osc.frequency.value = freq;
        const t = ctx.currentTime + start;
        gain.gain.setValueAtTime(0, t);
        gain.gain.linearRampToValueAtTime(0.55, t + 0.02);
        gain.gain.exponentialRampToValueAtTime(0.001, t + dur);
        osc.start(t);
        osc.stop(t + dur + 0.05);
      });

      // 尾音：低沉鑼聲感（低頻正弦 + 快速衰減）
      const gong = ctx.createOscillator();
      const gongGain = ctx.createGain();
      gong.connect(gongGain);
      gongGain.connect(master);
      gong.type = "sine";
      gong.frequency.setValueAtTime(180, ctx.currentTime + 0.42);
      gong.frequency.exponentialRampToValueAtTime(90, ctx.currentTime + 1.4);
      const gt = ctx.currentTime + 0.42;
      gongGain.gain.setValueAtTime(0, gt);
      gongGain.gain.linearRampToValueAtTime(0.7, gt + 0.02);
      gongGain.gain.exponentialRampToValueAtTime(0.001, gt + 1.2);
      gong.start(gt);
      gong.stop(gt + 1.3);
    } catch (_) {}
  }

  // ── 存入胡牌詳情快照 ──────────────────────────────────────
  if (winHistory.length > 0) {
    winHistory[0].snapshot = {
      name:  document.getElementById("win-player-name")?.innerHTML ?? "",
      type:  document.getElementById("win-type")?.innerHTML         ?? "",
      yaku:  document.getElementById("win-yaku")?.innerHTML         ?? "",
      score: document.getElementById("win-score")?.innerHTML        ?? "",
      hands: document.getElementById("win-all-hands")?.innerHTML    ?? "",
    };
  }

}

function log(message, type = "system") {
  const entry = document.createElement("div");
  entry.className = `log-entry ${type}`;
  entry.textContent = message;
  elLog.appendChild(entry);
  elLog.scrollTop = elLog.scrollHeight;
}

function resetScores() {
  scores = {
    [PLAYER_SOUTH]: INITIAL_SCORE,
    [AI_EAST]:      INITIAL_SCORE,
    [AI_WEST]:      INITIAL_SCORE,
  };
}

function updatePlayerNameUI() {
  // 更新座位標籤
  const seatNameEl = document.getElementById("south-seat-name");
  if (seatNameEl) seatNameEl.textContent = playerName;
  // 更新骰子結果中的全名
  SEAT_NAMES_FULL[PLAYER_SOUTH] = playerName;
  // 更新主頁資料卡
  refreshProfileCard();
}

function refreshProfileCard() {
  const nameEl      = document.getElementById("profile-name");
  const avatarEl    = document.getElementById("profile-avatar");
  const balanceEl   = document.getElementById("profile-balance");
  const gameAvatar  = document.getElementById("game-player-avatar");
  if (nameEl)      nameEl.textContent    = playerName;
  if (avatarEl)    avatarEl.textContent  = playerAvatar;
  if (balanceEl)   balanceEl.textContent = scores[PLAYER_SOUTH].toLocaleString();
  if (gameAvatar)  gameAvatar.textContent = playerAvatar;
  // 余額不再跨頁面持久化（每次回主頁會重置為初始值）
  // 頭像選項高亮當前選中
  document.querySelectorAll(".avatar-opt").forEach(btn => {
    btn.classList.toggle("active", btn.dataset.avatar === playerAvatar);
  });
}

// 頭像選擇器
document.getElementById("btn-pick-avatar").addEventListener("click", () => {
  const picker = document.getElementById("avatar-picker");
  picker.classList.toggle("hidden");
});
document.getElementById("btn-avatar-close").addEventListener("click", () => {
  document.getElementById("avatar-picker").classList.add("hidden");
});
document.getElementById("avatar-picker").addEventListener("click", (e) => {
  const btn = e.target.closest(".avatar-opt");
  if (!btn) return;
  playerAvatar = btn.dataset.avatar;
  localStorage.setItem("mj-player-avatar", playerAvatar);
  refreshProfileCard();
  document.getElementById("avatar-picker").classList.add("hidden");
});

// 資料卡內聯編輯名字
function startInlineNameEdit() {
  const nameEl = document.getElementById("profile-name");
  if (!nameEl || nameEl.querySelector("input")) return; // 已在編輯中
  const current = playerName || "玩家";
  const input = document.createElement("input");
  input.type = "text";
  input.value = current;
  input.maxLength = 12;
  input.className = "profile-name-inline-input";
  nameEl.textContent = "";
  nameEl.appendChild(input);
  input.focus();
  input.select();
  function save() {
    const val = input.value.trim() || "玩家";
    playerName    = val;
    nameConfirmed = true;
    localStorage.setItem("mj-player-name", val);
    updatePlayerNameUI();
    nameEl.textContent = val;
  }
  input.addEventListener("blur", save);
  input.addEventListener("keydown", (e) => {
    if (e.key === "Enter") { input.blur(); }
    if (e.key === "Escape") { nameEl.textContent = current; }
  });
}

document.getElementById("btn-edit-name").addEventListener("click", startInlineNameEdit);
document.getElementById("profile-name").addEventListener("click",   startInlineNameEdit);

// B：重置余額按鈕
const btnResetBalance = document.getElementById("btn-reset-balance");
if (btnResetBalance) {
  btnResetBalance.addEventListener("click", (e) => {
    e.stopPropagation();
    resetScores();
    localStorage.removeItem("mj-player-balance");
    refreshProfileCard();
    // 短暫動畫反饋
    btnResetBalance.textContent = "✓";
    setTimeout(() => { btnResetBalance.textContent = "↺"; }, 800);
  });
}

// 頁面初始化：同步 localStorage 的名字 / 頭像到資料卡和遊戲座位名
updatePlayerNameUI();

// ── 手機版：首次啟動姓名輸入覆蓋層（btn-confirm-name 僅存在於 mobile.html）──
(function wireMobileNameInput() {
  const overlay   = document.getElementById("name-input-overlay");
  const input     = document.getElementById("player-name-input");
  const confirmBtn = document.getElementById("btn-confirm-name");
  if (!overlay || !confirmBtn || !input) return; // PC 版沒有此元素，直接跳過

  function hideMobileNameOverlay() {
    overlay.classList.add("hidden");
  }

  function confirmMobileName() {
    const val = input.value.trim() || "玩家";
    playerName    = val;
    nameConfirmed = true;
    localStorage.setItem("mj-player-name", val);
    updatePlayerNameUI();
    refreshProfileCard();
    hideMobileNameOverlay();
  }

  confirmBtn.addEventListener("click", confirmMobileName);
  input.addEventListener("keydown", (e) => {
    if (e.key === "Enter") confirmMobileName();
  });

  // 首次進入時若未曾設定名字，自動彈出輸入框
  if (!nameConfirmed) {
    input.value = playerName !== "玩家" ? playerName : "";
    overlay.classList.remove("hidden");
  }
})();

function goHomeAfterBankrupt() {
  sessionOver = false;
  const noticeEl = document.getElementById("bankrupt-notice");
  if (noticeEl) noticeEl.classList.add("hidden");
  const closeBtn = document.getElementById("btn-close-win");
  if (closeBtn) closeBtn.textContent = "開始新局";
  resetState();
  resetScores(); // C：回主頁自動重置余額
  gameOver = true;
  render();
  document.getElementById("action-bar").style.display = "none";
  document.getElementById("win-overlay").classList.add("hidden");
  document.getElementById("home-screen").classList.remove("hidden");
  hideTopBar();
  refreshProfileCard();
}

function resetState() {
  wall = createThreePlayerWall(); // 三人牌山：移除Z4
  hands = {
    [PLAYER_SOUTH]: [],
    [AI_EAST]: [],
    [AI_WEST]: [],
  };
  discards = {
    [PLAYER_SOUTH]: [],
    [AI_EAST]: [],
    [AI_WEST]: [],
  };
  flowers = {
    [PLAYER_SOUTH]: [],
    [AI_EAST]: [],
    [AI_WEST]: [],
  };
  feis = {
    [PLAYER_SOUTH]: [],
    [AI_EAST]: [],
    [AI_WEST]: [],
  };
  melds = {
    [PLAYER_SOUTH]: [],
    [AI_EAST]: [],
    [AI_WEST]: [],
  };
  currentTurn = PLAYER_SOUTH;
  dealerPlayer = PLAYER_SOUTH; // 會在 actuallyStartGame 覆蓋
  drawnThisTurn = false;
  gameOver = false;
  afterKongDraw = false;
  turnCount = 0;
  lastDiscard = null;
  awaitingPlayerClaim = false;
  claimOptions = { chi: false, peng: false, gang: false, chiOptions: [] };
  pendingTurnAfterDiscard = null;
}

function dealInitialHands() {
  // 台灣 16 張：每家 16 張（三人版：3 家）
  const initialPerPlayer = 16;
  const players = [PLAYER_SOUTH, AI_EAST, AI_WEST];
  for (let i = 0; i < initialPerPlayer; i++) {
    for (let p of players) {
      drawOneTileToHandOrFlower(p);
      if (wall.length === 0) return;
    }
  }
  // 起手排序
  for (let p of players) {
    hands[p] = MJ.sortHand(hands[p]);
  }
}

function drawOneTileToHandOrFlower(player) {
  if (wall.length === 0) return null;
  const tile = wall.pop();
  if (!tile) return null;
  if (tile[0] === "F") {
    flowers[player].push(tile);
    log(`${getSeatName(player)}摸到花牌 ${formatTileLabel(tile)}，補一張。`, player === PLAYER_SOUTH ? "player" : "ai");
    return drawOneTileToHandOrFlower(player);
  }
  // 飛牌進入手牌（可作萬用牌）
  hands[player].push(tile);
  return tile;
}

function render() {
  elWallCount.textContent    = wall.length.toString();
  if (elWallCountBar) elWallCountBar.textContent = wall.length.toString();
  elCurrentPlayer.textContent =
    currentTurn === PLAYER_SOUTH ? playerName :
    currentTurn === AI_EAST      ? "人機 2" :
                                   "人機 1";

  // 顯示本局庄家（資訊欄短標籤 + 座位旁徽章）
  const dealerEl = document.getElementById("dealer-name");
  if (dealerEl) {
    const shortNames = {
      [PLAYER_SOUTH]: playerName,
      [AI_EAST]:      "人機 2",
      [AI_WEST]:      "人機 1",
    };
    dealerEl.textContent = shortNames[dealerPlayer] || "-";
  }

  // 座位旁的庄家徽章：只顯示當前庄家那一個
  const badgeMap = {
    [PLAYER_SOUTH]: "dealer-badge-south",
    [AI_EAST]:      "dealer-badge-east",
    [AI_WEST]:      "dealer-badge-west",
  };
  for (const [player, badgeId] of Object.entries(badgeMap)) {
    const badge = document.getElementById(badgeId);
    if (!badge) continue;
    if (player === dealerPlayer) {
      badge.classList.remove("hidden");
    } else {
      badge.classList.add("hidden");
    }
  }

  // 中央輪到指示器
  const compassMap = {
    [PLAYER_SOUTH]: "S",
    [AI_EAST]:      "E",
    [AI_WEST]:      "W",
  };
  const activeSeat = compassMap[currentTurn];
  document.querySelectorAll(".tc-arrow").forEach(el => {
    el.classList.toggle("tc-active", el.dataset.seat === activeSeat);
  });

  // 棄牌區標籤：只顯示固定文字，庄家標示移至座位旁的 dealer-badge
  const discardLabelBase = {
    [PLAYER_SOUTH]: ["dlabel-south", "南棄（你）"],
    [AI_EAST]:      ["dlabel-east",  "東棄"],
    [AI_WEST]:      ["dlabel-west",  "西棄"],
  };
  for (const [player, [labelId, baseText]] of Object.entries(discardLabelBase)) {
    const el = document.getElementById(labelId);
    if (el) el.textContent = baseText;
  }

  // 玩家手牌（支援拖拽排序）
  elPlayerHand.innerHTML = "";
  const handLen = hands[PLAYER_SOUTH].length;
  hands[PLAYER_SOUTH].forEach((tile, index) => {
    const div = renderTile(tile, true);
    // 剛摸的牌（最後一張）與其餘手牌拉開距離
    if (drawnThisTurn && index === handLen - 1) {
      div.classList.add("drawn-tile");
    }
    div.addEventListener("click", () => onPlayerDiscard(tile));

    // 只有飛牌可以拖拽重排位置
    if (tile[0] === "H") {
      div.draggable = true;
      div.dataset.idx = index;

      div.addEventListener("dragstart", (e) => {
        dragSrcIdx = index;
        e.dataTransfer.effectAllowed = "move";
        setTimeout(() => div.classList.add("dragging"), 0);
      });
      div.addEventListener("dragend", () => {
        div.classList.remove("dragging");
      });
    }

    // 所有牌都接受飛牌放入（drop target）
    div.addEventListener("dragover", (e) => {
      if (dragSrcIdx === -1) return;
      e.preventDefault();
      e.dataTransfer.dropEffect = "move";
      div.classList.add("drag-over");
    });
    div.addEventListener("dragleave", () => div.classList.remove("drag-over"));
    div.addEventListener("drop", (e) => {
      e.preventDefault();
      div.classList.remove("drag-over");
      if (dragSrcIdx !== -1 && dragSrcIdx !== index) {
        const hand = hands[PLAYER_SOUTH];
        const [moved] = hand.splice(dragSrcIdx, 1);
        hand.splice(index, 0, moved);
        dragSrcIdx = -1;
        render();
      }
    });

    elPlayerHand.appendChild(div);
  });

  // AI 手牌只顯示背面（三人版：無北家）
  renderAiHand(elAiEastHand, hands[AI_EAST].length);
  renderAiHand(elAiWestHand, hands[AI_WEST].length);

  // 分數顯示
  const scoreIds = {
    [PLAYER_SOUTH]: "score-south",
    [AI_EAST]:      "score-east",
    [AI_WEST]:      "score-west",
  };
  Object.entries(scoreIds).forEach(([pid, id]) => {
    const el = document.getElementById(id);
    if (el) el.textContent = scores[pid].toLocaleString();
  });

  // 棄牌
  renderDiscardRow(elDiscardSouth, discards[PLAYER_SOUTH], PLAYER_SOUTH);
  renderDiscardRow(elDiscardEast,  discards[AI_EAST],     AI_EAST);
  renderDiscardRow(elDiscardWest,  discards[AI_WEST],     AI_WEST);

  // 花牌（三人版：無北家）
  renderFlowersRow(elFlowersSouth, flowers[PLAYER_SOUTH]);
  renderFlowersRow(elFlowersEast, flowers[AI_EAST]);
  renderFlowersRow(elFlowersWest, flowers[AI_WEST]);

  renderFlowersRow(elFeisSouth, feis[PLAYER_SOUTH]);
  renderFlowersRow(elFeisEast, feis[AI_EAST]);
  renderFlowersRow(elFeisWest, feis[AI_WEST]);

  // 副露（碰/槓，三人版無吃）
  renderMeldsRow(elMeldsSouth, melds[PLAYER_SOUTH]);
  renderMeldsRow(elMeldsEast, melds[AI_EAST]);
  renderMeldsRow(elMeldsWest, melds[AI_WEST]);

  // 行動按鈕：用 show/hide 取代 disabled，只在有動作時才出現
  function setBtn(btn, visible) {
    btn.style.display = visible ? "" : "none";
    btn.disabled = !visible;
  }

  const canDraw = currentTurn === PLAYER_SOUTH && !drawnThisTurn && !gameOver && !awaitingPlayerClaim;

  // 自摸胡：已摸牌，手牌數 ≡ 2 (mod 3)，且確實成胡
  const canZimo = !gameOver && currentTurn === PLAYER_SOUTH && !awaitingPlayerClaim &&
    drawnThisTurn && hands[PLAYER_SOUTH].length % 3 === 2 &&
    MJ.isWinningHand(hands[PLAYER_SOUTH]);
  // 榮胡：別人打出的牌加入後手牌數 ≡ 2 (mod 3)，且確實成胡
  const canRonghu = !gameOver && awaitingPlayerClaim && !!lastDiscard &&
    (hands[PLAYER_SOUTH].length + 1) % 3 === 2 &&
    MJ.isWinningHand([...hands[PLAYER_SOUTH], lastDiscard.tile]);

  const canConcealedGang =
    !awaitingPlayerClaim && !gameOver &&
    currentTurn === PLAYER_SOUTH && drawnThisTurn &&
    (!!findConcealedGangTile() || !!findAddKongTile());

  const canSwap = !gameOver && currentTurn === PLAYER_SOUTH && drawnThisTurn && !!findFeiSwapOption();

  // 聽牌按鈕：輪到玩家且已摸牌時可用（自摸胡時不顯示，已胡就不需要聽牌了）
  const canTenpai = !gameOver && currentTurn === PLAYER_SOUTH && drawnThisTurn &&
    !canZimo && !awaitingPlayerClaim;

  if (btnDraw) setBtn(btnDraw, canDraw);
  setBtn(btnWin,     canZimo || canRonghu);
  // 三人麻將：無吃牌(btnChi 不存在，安全跳過)
  if (btnChi) setBtn(btnChi, false);
  setBtn(btnPeng,    awaitingPlayerClaim && claimOptions.peng);
  setBtn(btnGang,    (awaitingPlayerClaim && claimOptions.gang) || canConcealedGang);
  setBtn(btnSwapFei, canSwap);
  setBtn(btnTenpai,  canTenpai);
  setBtn(btnPass,    !!awaitingPlayerClaim);
  const canRecommend = !gameOver && currentTurn === PLAYER_SOUTH && drawnThisTurn && !awaitingPlayerClaim;
  if (btnRecommend) setBtn(btnRecommend, canRecommend);

  btnWin.classList.toggle("win-ready", canZimo || canRonghu);

  // 顯示/隱藏整個 action bar
  const actionBarEl = document.getElementById("action-bar");
  const anyVisible = [btnDraw, btnWin, btnPeng, btnGang, btnSwapFei, btnTenpai, btnPass, btnRecommend]
    .some(b => b && b.style.display !== "none");
  actionBarEl.style.display = anyVisible ? "flex" : "none";

  // 鍵盤選中高亮
  applyKbdHighlight();

  // 每次渲染後重新計算縮放比（牌數/副露可能改變桌面尺寸）
  requestAnimationFrame(fitTable);
}

/** 把 kbdSelIdx 對應的手牌加上 .kbd-selected 高亮 */
function applyKbdHighlight() {
  if (!elPlayerHand) return;
  const tiles = elPlayerHand.querySelectorAll(".tile.player");
  const hand   = hands[PLAYER_SOUTH];
  if (currentTurn !== PLAYER_SOUTH || !hand || hand.length === 0) {
    kbdSelIdx = -1;
  }
  if (kbdSelIdx >= (hand ? hand.length : 0)) kbdSelIdx = -1;
  tiles.forEach((el, i) => el.classList.toggle("kbd-selected", i === kbdSelIdx));
}

// ── 推薦打法 ──────────────────────────────────────────────────────
let _recTile = null;

function clearRecommend() {
  _recTile = null;
  if (elPlayerHand) {
    elPlayerHand.querySelectorAll(".tile.player").forEach(el => el.classList.remove("recommend-tile"));
  }
  const ov = document.getElementById("recommend-overlay");
  if (ov) ov.style.display = "none";
}

function showRecommendation() {
  const hand = hands[PLAYER_SOUTH];
  if (!hand || hand.length === 0) return;

  const overlay = document.getElementById("recommend-overlay");
  const body    = document.getElementById("recommend-body");
  if (!overlay || !body) return;
  body.innerHTML = "";

  if (MJ.isWinningHand(hand)) {
    body.innerHTML = `<p class="tenpai-none" style="color:#ffe066;">✅ 手牌已成胡！請點「胡」按鈕宣告自摸。</p>`;
    overlay.style.display = "flex";
    return;
  }

  const tenpaiOpts = findTenpaiOptions(hand);

  if (tenpaiOpts.length > 0) {
    tenpaiOpts.forEach(({ discard, winTiles }, i) => {
      const row = document.createElement("div");
      row.className = "tenpai-row" + (i === 0 ? " rec-best-row" : "");

      if (i === 0) {
        const badge = document.createElement("span");
        badge.className = "rec-badge";
        badge.textContent = "推薦";
        row.appendChild(badge);
      }

      const discardWrap = document.createElement("div");
      discardWrap.className = "tenpai-discard-wrap";
      const discardLabel = document.createElement("span");
      discardLabel.className = "tenpai-label";
      discardLabel.textContent = "打出";
      discardWrap.appendChild(discardLabel);
      discardWrap.appendChild(renderTile(discard, ["player", "tenpai-tile"]));

      const arrow = document.createElement("span");
      arrow.className = "tenpai-arrow";
      arrow.textContent = "→";

      const waitWrap = document.createElement("div");
      waitWrap.className = "tenpai-wait-wrap";
      const waitLabel = document.createElement("span");
      waitLabel.className = "tenpai-label";
      waitLabel.textContent = `聽（${winTiles.length} 種）`;
      const waitTiles = document.createElement("div");
      waitTiles.className = "tenpai-wait-tiles";
      winTiles.forEach(t => waitTiles.appendChild(renderTile(t, ["player", "tenpai-tile"])));
      waitWrap.appendChild(waitLabel);
      waitWrap.appendChild(waitTiles);

      row.appendChild(discardWrap);
      row.appendChild(arrow);
      row.appendChild(waitWrap);
      body.appendChild(row);
    });

    _recTile = tenpaiOpts[0].discard;
  } else {
    const recTile = chooseAiDiscardHard(hand);
    _recTile = recTile;

    const row = document.createElement("div");
    row.className = "tenpai-row rec-best-row";

    const badge = document.createElement("span");
    badge.className = "rec-badge";
    badge.textContent = "建議";
    row.appendChild(badge);

    const discardWrap = document.createElement("div");
    discardWrap.className = "tenpai-discard-wrap";
    const discardLabel = document.createElement("span");
    discardLabel.className = "tenpai-label";
    discardLabel.textContent = "打出";
    discardWrap.appendChild(discardLabel);
    discardWrap.appendChild(renderTile(recTile, ["player", "tenpai-tile"]));

    const hint = document.createElement("span");
    hint.className = "tenpai-label";
    hint.style.cssText = "color:#aaa;margin-left:12px;";
    hint.textContent = "改善手牌，最接近聽牌";

    row.appendChild(discardWrap);
    row.appendChild(hint);
    body.appendChild(row);
  }

  if (elPlayerHand && _recTile) {
    const tiles = elPlayerHand.querySelectorAll(".tile.player");
    const idx   = hand.indexOf(_recTile);
    tiles.forEach((el, i) => el.classList.toggle("recommend-tile", i === idx));
    kbdSelIdx = idx;
    applyKbdHighlight();
  }

  overlay.style.display = "flex";
}

// 筒 (P) dot positions in a 3×3 grid (index 0=top-left … 8=bottom-right)
// 3×3 格子位置（0=TL … 8=BR）
const PIN_POSITIONS = [
  [],
  [4],                                   // 1 – 中央（特殊大圓）
  [1, 7],                                // 2 – 上中, 下中
  [0, 4, 8],                             // 3 – 對角
  [0, 2, 6, 8],                          // 4 – 四角
  [0, 2, 4, 6, 8],                       // 5 – 四角+中
  [0, 2, 3, 5, 6, 8],                    // 6 – 兩欄
  [0, 2, 3, 4, 5, 6, 8],                 // 7 – 兩欄+中
  [0, 1, 2, 3, 5, 6, 7, 8],             // 8 – 環形
  [0, 1, 2, 3, 4, 5, 6, 7, 8],          // 9 – 全滿
];

// 各點顏色：b=藍, r=紅, g=綠, b1=特殊1筒
const PIN_COLORS = [
  [],
  ["b1"],                                               // 1
  ["b", "g"],                                           // 2
  ["b", "r", "b"],                                      // 3
  ["g", "g", "b", "b"],                                 // 4
  ["g", "g", "r", "b", "b"],                            // 5
  ["g", "g", "r", "r", "r", "r"],                        // 6 – 上2綠 下4紅
  ["g", "g", "g", "r", "r", "r", "r"],                  // 7 – 上3綠 下4紅
  ["b", "b", "b", "b", "b", "b", "b", "b"],             // 8 – 2欄×4行 全藍
  ["g", "b", "g", "b", "r", "b", "g", "b", "g"],        // 9
];

// 建立單個筒 SVG（同心圓 / 特殊花圓）
function createPinSvgCircle(colorKey) {
  const ns = "http://www.w3.org/2000/svg";
  const svg = document.createElementNS(ns, "svg");
  svg.setAttribute("viewBox", "0 0 20 20");
  svg.setAttribute("class", `pin-circle pin-c-${colorKey}`);

  const mk = (tag, attrs) => {
    const el = document.createElementNS(ns, tag);
    for (const [k, v] of Object.entries(attrs)) el.setAttribute(k, v);
    return el;
  };

  if (colorKey === "b1") {
    // 特殊 1筒：花圓（外邊框 + 6瓣 + 紅心）
    svg.appendChild(mk("circle", { cx:"10", cy:"10", r:"9",   class:"pin-r1" }));
    svg.appendChild(mk("circle", { cx:"10", cy:"10", r:"7.2", class:"pin-r2" }));
    svg.appendChild(mk("circle", { cx:"10", cy:"10", r:"5.8", class:"pin-r3" }));
    for (let i = 0; i < 6; i++) {
      const a = (i * Math.PI * 2) / 6 - Math.PI / 2;
      svg.appendChild(mk("circle", {
        cx: (10 + Math.cos(a) * 3.5).toFixed(2),
        cy: (10 + Math.sin(a) * 3.5).toFixed(2),
        r: "1.7", class: "pin-petal",
      }));
    }
    svg.appendChild(mk("circle", { cx:"10", cy:"10", r:"2",   class:"pin-ctr" }));
  } else {
    // 一般筒：4層同心圓
    svg.appendChild(mk("circle", { cx:"10", cy:"10", r:"9",   class:"pin-r1" }));  // 外環
    svg.appendChild(mk("circle", { cx:"10", cy:"10", r:"7",   class:"pin-r2" }));  // 白圈
    svg.appendChild(mk("circle", { cx:"10", cy:"10", r:"5",   class:"pin-r3" }));  // 內環
    svg.appendChild(mk("circle", { cx:"10", cy:"10", r:"2.8", class:"pin-r4" }));  // 內白
    svg.appendChild(mk("circle", { cx:"10", cy:"10", r:"1.5", class:"pin-ctr" })); // 中心點
  }
  return svg;
}

// 建立分段堆疊排版：sections = 每段顏色陣列，例如 [["g","g"],["r","r","r","r"]]
function createPinStack(sections) {
  const wrap = document.createElement("div");
  wrap.className = "pin-grid pin-stack";
  sections.forEach(colors => {
    const row = document.createElement("div");
    row.className = `pin-stack-row pin-stack-${colors.length}`;
    colors.forEach(c => {
      const cell = document.createElement("div");
      cell.className = "pin-cell";
      cell.appendChild(createPinSvgCircle(c));
      row.appendChild(cell);
    });
    wrap.appendChild(row);
  });
  return wrap;
}

function createPinDots(count) {
  // 1筒：特殊大花圓，整格顯示
  if (count === 1) {
    const wrap = document.createElement("div");
    wrap.className = "pin-grid pin-single";
    wrap.appendChild(createPinSvgCircle("b1"));
    return wrap;
  }

  // 6筒：上2綠 + 下4紅（flex 縱向堆疊）
  if (count === 6) {
    return createPinStack([["g","g"], ["r","r","r","r"]]);
  }

  // 7筒：上3綠 + 下4紅（flex 縱向堆疊）
  if (count === 7) {
    return createPinStack([["g","g","g"], ["r","r","r","r"]]);
  }

  // 8筒：2欄 × 4行（不走 3×3 格子）
  if (count === 8) {
    const grid = document.createElement("div");
    grid.className = "pin-grid pin-grid-2x4";
    const colors = PIN_COLORS[8];
    colors.forEach(c => {
      const cell = document.createElement("div");
      cell.className = "pin-cell";
      cell.appendChild(createPinSvgCircle(c));
      grid.appendChild(cell);
    });
    return grid;
  }

  const grid = document.createElement("div");
  grid.className = "pin-grid";
  const positions = PIN_POSITIONS[count] || [];
  const colors    = PIN_COLORS[count]    || [];
  const filled    = new Set(positions);
  let ci = 0;
  for (let i = 0; i < 9; i++) {
    const cell = document.createElement("div");
    cell.className = "pin-cell";
    if (filled.has(i)) {
      cell.appendChild(createPinSvgCircle(colors[ci++] || "b"));
    }
    grid.appendChild(cell);
  }
  return grid;
}

// 花牌 SVG 插圖（16種）
function createFlowerSvg(val) {
  const ns = "http://www.w3.org/2000/svg";
  const svg = document.createElementNS(ns, "svg");
  svg.setAttribute("viewBox", "0 0 28 34");
  svg.setAttribute("preserveAspectRatio", "xMidYMid meet");
  svg.style.cssText = "width:100%;height:100%;display:block;overflow:visible";

  const mk = (tag, attrs) => {
    const el = document.createElementNS(ns, tag);
    Object.entries(attrs).forEach(([k,v]) => el.setAttribute(k, v));
    return el;
  };
  // 花瓣輔助
  const petals = (cx, cy, n, r, rx, ry, fill) => {
    for (let i = 0; i < n; i++) {
      const g = document.createElementNS(ns, "g");
      g.setAttribute("transform", `rotate(${i*(360/n)},${cx},${cy})`);
      g.appendChild(mk("ellipse", {cx:String(cx), cy:String(cy-r), rx:String(rx), ry:String(ry), fill}));
      svg.appendChild(g);
    }
  };
  // 葉片
  const leaf = (d, fill="#2d8020") => svg.appendChild(mk("path", {d, fill, stroke:"#1a5010","stroke-width":"0.3"}));
  // 枝幹
  const branch = (d, col="#7a4010") => svg.appendChild(mk("path", {d, stroke:col,"stroke-width":"1.5",fill:"none","stroke-linecap":"round"}));

  switch(val) {
    /* ── 春夏秋冬 F1-F4（紅色系）── */
    case 1: // 春：花朵＋嫩葉
      branch("M14 33 Q14 26 14 20");
      leaf("M14 26 Q7 22 5 17 Q10 19 14 26");
      leaf("M14 26 Q21 22 23 17 Q18 19 14 26");
      petals(14,14,5,7,2.8,5.5,"#e82020");
      svg.appendChild(mk("circle",{cx:"14",cy:"14",r:"2.8",fill:"#ffd020"}));
      break;
    case 2: // 夏：荷花
      branch("M14 33 Q14 24 14 16");
      leaf("M14 24 Q5 20 3 13 Q9 17 14 24");
      leaf("M14 24 Q23 20 25 13 Q19 17 14 24");
      svg.appendChild(mk("ellipse",{cx:"14",cy:"10",rx:"6",ry:"3",fill:"#f06080",stroke:"#c03060","stroke-width":"0.5"}));
      petals(14,14,6,6,2.2,5,"#f08090");
      svg.appendChild(mk("circle",{cx:"14",cy:"14",r:"2.5",fill:"#ffe040"}));
      break;
    case 3: // 秋：楓葉枝
      branch("M4 33 Q10 26 14 20 Q18 14 22 8");
      branch("M14 20 Q8 16 6 11");
      [[22,8],[6,11],[14,20]].forEach(([x,y])=>{
        petals(x,y,5,4,2,4,"#e04010");
        svg.appendChild(mk("circle",{cx:String(x),cy:String(y),r:"1.5",fill:"#ffc020"}));
      });
      break;
    case 4: // 冬：梅枝
      branch("M6 33 Q12 26 14 20 Q16 14 20 9");
      branch("M14 20 Q20 17 23 19");
      [[20,9],[23,19],[14,20]].forEach(([x,y])=>{
        petals(x,y,5,4.5,2.2,4,"#ffaacc");
        svg.appendChild(mk("circle",{cx:String(x),cy:String(y),r:"1.5",fill:"#ffe0a0"}));
      });
      break;

    /* ── 梅蘭竹菊 F5-F8（墨綠系）── */
    case 5: // 梅：大梅花
      branch("M14 33 Q14 27 14 22");
      branch("M14 22 Q7 18 5 14");
      branch("M14 22 Q21 18 23 14");
      petals(14,12,5,7,3,5.5,"#e03060");
      svg.appendChild(mk("circle",{cx:"14",cy:"12",r:"3",fill:"#ffd040"}));
      for(let i=0;i<5;i++){
        const a=i*72*Math.PI/180;
        svg.appendChild(mk("circle",{cx:String(14+2.5*Math.sin(a)),cy:String(12-2.5*Math.cos(a)),r:"0.7",fill:"#e08020"}));
      }
      break;
    case 6: // 蘭：蘭草
      svg.appendChild(mk("path",{d:"M14 33 Q10 24 6 12",stroke:"#2d8020","stroke-width":"2",fill:"none","stroke-linecap":"round"}));
      svg.appendChild(mk("path",{d:"M14 33 Q16 22 20 8",stroke:"#2d8020","stroke-width":"2",fill:"none","stroke-linecap":"round"}));
      svg.appendChild(mk("path",{d:"M14 30 Q12 22 10 14",stroke:"#3a9a28","stroke-width":"1.5",fill:"none","stroke-linecap":"round"}));
      petals(20,10,5,4.5,2,4.5,"#c06ab8");
      svg.appendChild(mk("circle",{cx:"20",cy:"10",r:"2",fill:"#ffe060"}));
      break;
    case 7: // 竹：竹節
      [7,14,21].forEach((x,idx)=>{
        const col=idx===1?"#2d8a20":"#3aaa28";
        svg.appendChild(mk("rect",{x:String(x-2),y:"3",width:"4",height:"30",rx:"2",fill:col}));
        [10,18,26].forEach(jy=>svg.appendChild(mk("rect",{x:String(x-2.5),y:String(jy-1),width:"5",height:"2",rx:"1",fill:"#1a5a10"})));
      });
      svg.appendChild(mk("path",{d:"M14 3 Q6 0 4 2",stroke:"#2d8a20","stroke-width":"1.5",fill:"none"}));
      svg.appendChild(mk("path",{d:"M14 3 Q22 0 24 2",stroke:"#2d8a20","stroke-width":"1.5",fill:"none"}));
      break;
    case 8: // 菊：菊花
      branch("M14 33 Q14 26 14 21");
      leaf("M14 27 Q7 23 6 18 Q11 20 14 27");
      leaf("M14 27 Q21 23 22 18 Q17 20 14 27");
      petals(14,12,12,7,1.8,6.5,"#e07020");
      petals(14,12,12,4,1.2,3.5,"#ffe060");
      svg.appendChild(mk("circle",{cx:"14",cy:"12",r:"2.5",fill:"#ffd000"}));
      break;

    /* ── 琴棋書畫 F9-F12（墨色系）── */
    case 9: // 琴：古琴
      svg.appendChild(mk("path",{d:"M9 5 Q7 5 6 7 L6 29 Q6 31 9 31 L19 31 Q22 31 22 29 L22 7 Q22 5 19 5 Z",fill:"#7a3a10",stroke:"#4a2008","stroke-width":"0.6"}));
      svg.appendChild(mk("rect",{x:"11",y:"1",width:"6",height:"6",rx:"2",fill:"#5a2808"}));
      for(let i=0;i<6;i++){const x=9+i*2.2;svg.appendChild(mk("line",{x1:String(x),y1:"7",x2:String(x),y2:"29",stroke:"#c8a040","stroke-width":"0.5"}));}
      svg.appendChild(mk("rect",{x:"6",y:"25",width:"16",height:"1.5",rx:"0.5",fill:"#4a2008"}));
      break;
    case 10: // 棋：棋盤
      svg.appendChild(mk("rect",{x:"3",y:"3",width:"22",height:"22",fill:"#d4a040",stroke:"#8B4000","stroke-width":"1"}));
      [7,11,15,19,23].forEach(x=>svg.appendChild(mk("line",{x1:String(x),y1:"3",x2:String(x),y2:"25",stroke:"#4a2000","stroke-width":"0.5"})));
      [7,11,15,19,23].forEach(y=>svg.appendChild(mk("line",{x1:"3",y1:String(y),x2:"25",y2:String(y),stroke:"#4a2000","stroke-width":"0.5"})));
      svg.appendChild(mk("circle",{cx:"7",cy:"7",r:"2.5",fill:"#1a1a1a"}));
      svg.appendChild(mk("circle",{cx:"15",cy:"11",r:"2.5",fill:"#f0f0f0",stroke:"#999","stroke-width":"0.5"}));
      svg.appendChild(mk("circle",{cx:"11",cy:"19",r:"2.5",fill:"#1a1a1a"}));
      svg.appendChild(mk("circle",{cx:"19",cy:"15",r:"2.5",fill:"#f0f0f0",stroke:"#999","stroke-width":"0.5"}));
      svg.appendChild(mk("rect",{x:"5",y:"25",width:"18",height:"3",rx:"1",fill:"#8B4000"}));
      break;
    case 11: // 書：書本
      svg.appendChild(mk("rect",{x:"5",y:"5",width:"18",height:"24",rx:"1",fill:"#f5e8c0",stroke:"#8B4000","stroke-width":"1"}));
      svg.appendChild(mk("rect",{x:"4",y:"5",width:"4",height:"24",rx:"1",fill:"#8B4000"}));
      [10,14,18,22,26].forEach(y=>svg.appendChild(mk("line",{x1:"11",y1:String(y),x2:"22",y2:String(y),stroke:"#6a4020","stroke-width":"0.7"})));
      svg.appendChild(mk("rect",{x:"11",y:"6",width:"10",height:"5",fill:"#e8d098",stroke:"#8B4000","stroke-width":"0.5"}));
      break;
    case 12: // 畫：山水捲軸
      svg.appendChild(mk("rect",{x:"3",y:"3",width:"22",height:"3",rx:"1.5",fill:"#8B4000"}));
      svg.appendChild(mk("rect",{x:"5",y:"6",width:"18",height:"22",fill:"#f5e8c0",stroke:"#c8a070","stroke-width":"0.5"}));
      svg.appendChild(mk("path",{d:"M5 28 Q9 16 14 21 Q18 13 23 28 Z",fill:"#4a7a30",stroke:"#2a5010","stroke-width":"0.5"}));
      svg.appendChild(mk("circle",{cx:"20",cy:"10",r:"2.5",fill:"#e08820"}));
      svg.appendChild(mk("path",{d:"M5 22 Q8 18 11 22 Q14 18 17 22",stroke:"#5080c0","stroke-width":"1",fill:"none"}));
      svg.appendChild(mk("rect",{x:"3",y:"28",width:"22",height:"3",rx:"1.5",fill:"#8B4000"}));
      break;

    /* ── 貓雞蟲鼠 F13-F16（動物）── */
    case 13: // 貓
      svg.appendChild(mk("ellipse",{cx:"14",cy:"26",rx:"8",ry:"7",fill:"#c8a868"}));
      svg.appendChild(mk("circle",{cx:"14",cy:"15",r:"7",fill:"#c8a868"}));
      svg.appendChild(mk("polygon",{points:"8,11 11,4 14,11",fill:"#c8a868"}));
      svg.appendChild(mk("polygon",{points:"14,11 17,4 20,11",fill:"#c8a868"}));
      svg.appendChild(mk("polygon",{points:"9,11 11,6 13,11",fill:"#e8b0a0"}));
      svg.appendChild(mk("polygon",{points:"15,11 17,6 19,11",fill:"#e8b0a0"}));
      svg.appendChild(mk("ellipse",{cx:"11",cy:"14",rx:"1.5",ry:"2",fill:"#1a1a1a"}));
      svg.appendChild(mk("ellipse",{cx:"17",cy:"14",rx:"1.5",ry:"2",fill:"#1a1a1a"}));
      svg.appendChild(mk("polygon",{points:"14,17 13,19 15,19",fill:"#e06060"}));
      ["6,18,12,18","16,18,22,18","6,20,12,19","16,19,22,20"].forEach(pts=>{
        const [x1,y1,x2,y2]=pts.split(",");
        svg.appendChild(mk("line",{x1,y1,x2,y2,stroke:"#aaa","stroke-width":"0.5"}));
      });
      break;
    case 14: // 雞
      svg.appendChild(mk("ellipse",{cx:"13",cy:"25",rx:"9",ry:"8",fill:"#d07818"}));
      svg.appendChild(mk("circle",{cx:"20",cy:"15",r:"6",fill:"#d07818"}));
      svg.appendChild(mk("path",{d:"M19 9 Q21 6 23 8 Q22 5 25 6 Q23 3 26 4",stroke:"#c82010","stroke-width":"2",fill:"none","stroke-linecap":"round"}));
      svg.appendChild(mk("polygon",{points:"26,16 24,15 24,17",fill:"#e09020"}));
      svg.appendChild(mk("circle",{cx:"22",cy:"14",r:"1.5",fill:"#1a1a1a"}));
      svg.appendChild(mk("ellipse",{cx:"25",cy:"19",rx:"2",ry:"1.5",fill:"#c82010"}));
      svg.appendChild(mk("path",{d:"M5 21 Q1 17 2 13 M4 24 Q0 21 1 17",stroke:"#2d6a20","stroke-width":"2",fill:"none","stroke-linecap":"round"}));
      svg.appendChild(mk("line",{x1:"11",y1:"33",x2:"10",y2:"35",stroke:"#e09020","stroke-width":"2"}));
      svg.appendChild(mk("line",{x1:"16",y1:"33",x2:"17",y2:"35",stroke:"#e09020","stroke-width":"2"}));
      break;
    case 15: // 蟲（毛毛蟲）
      [31,26,21,16,11].forEach((y,i)=>{
        const x=14+(i%2===0?0:2), col=i%2===0?"#3a9a20":"#2d7818";
        svg.appendChild(mk("circle",{cx:String(x),cy:String(y),r:"3.5",fill:col,stroke:"#1a5010","stroke-width":"0.4"}));
      });
      svg.appendChild(mk("circle",{cx:"16",cy:"7",r:"4.5",fill:"#3a9a20",stroke:"#1a5010","stroke-width":"0.4"}));
      svg.appendChild(mk("circle",{cx:"14.5",cy:"6",r:"1",fill:"#1a1a1a"}));
      svg.appendChild(mk("circle",{cx:"17.5",cy:"6",r:"1",fill:"#1a1a1a"}));
      svg.appendChild(mk("line",{x1:"14",y1:"3",x2:"11",y2:"0",stroke:"#2d7818","stroke-width":"0.8"}));
      svg.appendChild(mk("line",{x1:"18",y1:"3",x2:"21",y2:"0",stroke:"#2d7818","stroke-width":"0.8"}));
      svg.appendChild(mk("circle",{cx:"11",cy:"0",r:"1",fill:"#2d7818"}));
      svg.appendChild(mk("circle",{cx:"21",cy:"0",r:"1",fill:"#2d7818"}));
      break;
    case 16: // 鼠
      svg.appendChild(mk("ellipse",{cx:"13",cy:"25",rx:"8",ry:"8",fill:"#909098"}));
      svg.appendChild(mk("ellipse",{cx:"20",cy:"15",rx:"6",ry:"5",fill:"#909098"}));
      svg.appendChild(mk("ellipse",{cx:"25",cy:"17",rx:"3",ry:"2",fill:"#b0b0b8"}));
      svg.appendChild(mk("circle",{cx:"18",cy:"10",r:"3.5",fill:"#909098",stroke:"#606068","stroke-width":"0.5"}));
      svg.appendChild(mk("circle",{cx:"18",cy:"10",r:"2",fill:"#e8a0a0"}));
      svg.appendChild(mk("circle",{cx:"22",cy:"14",r:"1.5",fill:"#1a1a1a"}));
      svg.appendChild(mk("circle",{cx:"22.5",cy:"13.5",r:"0.4",fill:"white"}));
      svg.appendChild(mk("circle",{cx:"27",cy:"17",r:"1",fill:"#d06060"}));
      svg.appendChild(mk("path",{d:"M5 27 Q1 23 3 19 Q5 15 3 13",stroke:"#909098","stroke-width":"1.5",fill:"none","stroke-linecap":"round"}));
      svg.appendChild(mk("line",{x1:"10",y1:"33",x2:"8",y2:"35",stroke:"#b0b0b8","stroke-width":"1.5"}));
      svg.appendChild(mk("line",{x1:"16",y1:"33",x2:"17",y2:"35",stroke:"#b0b0b8","stroke-width":"1.5"}));
      break;
  }
  return svg;
}

// 白板 SVG：同心圓角方框
function createBaiSvg() {
  const ns = "http://www.w3.org/2000/svg";
  const svg = document.createElementNS(ns, "svg");
  svg.setAttribute("viewBox", "0 0 52 72");
  svg.setAttribute("preserveAspectRatio", "xMidYMid meet");
  svg.style.width = "100%";
  svg.style.height = "100%";
  svg.style.display = "block";

  const mk = (tag, attrs) => {
    const el = document.createElementNS(ns, tag);
    Object.entries(attrs).forEach(([k, v]) => el.setAttribute(k, v));
    return el;
  };

  // 外框
  svg.appendChild(mk("rect", { x:"3", y:"3", width:"46", height:"66", rx:"6", ry:"6",
    fill:"none", stroke:"#1a1a1a", "stroke-width":"2.5" }));
  // 中框
  svg.appendChild(mk("rect", { x:"8", y:"8", width:"36", height:"56", rx:"4", ry:"4",
    fill:"none", stroke:"#1a1a1a", "stroke-width":"2" }));
  // 四個角落小弧線（左上、右上、左下、右下）
  const arcs = [
    "M 8 17 A 9 9 0 0 1 17 8",
    "M 35 8 A 9 9 0 0 1 44 17",
    "M 44 55 A 9 9 0 0 1 35 64",
    "M 17 64 A 9 9 0 0 1 8 55",
  ];
  arcs.forEach(d => {
    svg.appendChild(mk("path", { d, fill:"none", stroke:"#1a1a1a", "stroke-width":"2",
      "stroke-linecap":"round" }));
  });

  return svg;
}

// 建立單根索子 SVG（I 字形：上橫 + 直幹 + 下橫）
function createBamSvgStick(isRed, isCenter, rotateDeg) {
  const ns = "http://www.w3.org/2000/svg";
  const svg = document.createElementNS(ns, "svg");
  svg.setAttribute("viewBox", "0 0 10 28");
  svg.setAttribute("preserveAspectRatio", "xMidYMid meet");
  let cls = "bam-stick";
  if (isRed)    cls += " bam-red";
  if (isCenter) cls += " bam-center";
  svg.setAttribute("class", cls);
  if (rotateDeg) svg.style.transform = `rotate(${rotateDeg}deg)`;

  const mk = (tag, attrs) => {
    const el = document.createElementNS(ns, tag);
    for (const [k, v] of Object.entries(attrs)) el.setAttribute(k, v);
    return el;
  };

  // 純竪線條（｜）
  svg.appendChild(mk("rect", { x:"3.5", y:"1", width:"3", height:"26", class:"bam-body", rx:"1.5" }));
  // 高光
  svg.appendChild(mk("rect", { x:"4.1", y:"2", width:"0.8", height:"24", class:"bam-shine" }));
  return svg;
}

// 定義每張條牌的排列：cols=欄數, colors: g=綠, r=紅, c=紅且跨欄居中
const BAM_PATTERNS = {
  1: { cols: 1, colors: ["g"] },
  2: { cols: 1, colors: ["g","g"] },
  3: { cols: 1, colors: ["g","g","g"] },
  4: { cols: 2, colors: ["g","g","g","g"] },
  5: { cols: 2, colors: ["g","g","c","g","g"] },   // 中間紅居中
  6: { cols: 2, colors: ["g","g","g","g","g","g"] },
  7: { cols: 2, colors: ["c","g","g","g","g","g","g"] }, // 頂部紅居中
  8: { cols: 2, colors: ["g","g","g","g","g","g","g","g"] },
  9: { cols: 3, colors: ["g","g","g","g","g","g","g","g","g"] },
};

// 建立分段堆疊索子：sections = [[color,...], ...]
function createBamStack(sections) {
  const wrap = document.createElement("div");
  wrap.className = "tile-bamboo bam-stack";
  sections.forEach(colors => {
    const row = document.createElement("div");
    row.className = `bam-stack-row bam-stack-${colors.length}`;
    colors.forEach(c => {
      row.appendChild(createBamSvgStick(c === "r" || c === "c", false));
    });
    wrap.appendChild(row);
  });
  return wrap;
}

function createBambooSticks(count) {
  // 3索：頂1綠居中 + 下2綠
  if (count === 3) {
    return createBamStack([["g"], ["g","g"]]);
  }

  // 5索：上2綠 + 中1紅 + 下2綠（分段堆疊）
  if (count === 5) {
    return createBamStack([["g","g"], ["c"], ["g","g"]]);
  }
  // 6索：3×2 排列（上排3綠 + 下排3綠）
  if (count === 6) {
    return createBamStack([["g","g","g"], ["g","g","g"]]);
  }

  // 7索：頂1紅居中 + 中3綠 + 下3綠
  if (count === 7) {
    return createBamStack([["c"], ["g","g","g"], ["g","g","g"]]);
  }

  // 8索：上排 |/\| + 下排 |\/|
  if (count === 8) {
    const wrap = document.createElement("div");
    wrap.className = "tile-bamboo bam-stack";
    // 每排的旋轉角度：0=直，-45=/ ，+45=\
    const rows = [
      [0, -45, 45, 0],
      [0,  45, -45, 0],
    ];
    rows.forEach(angles => {
      const row = document.createElement("div");
      row.className = "bam-stack-row bam-stack-4";
      angles.forEach(deg => {
        row.appendChild(createBamSvgStick(false, false, deg));
      });
      wrap.appendChild(row);
    });
    return wrap;
  }

  // 9索：3×3，中間一列全紅，其餘綠
  if (count === 9) {
    return createBamStack([["g","r","g"], ["g","r","g"], ["g","r","g"]]);
  }

  const pattern = BAM_PATTERNS[count] || { cols: 2, colors: Array(count).fill("g") };
  const wrap = document.createElement("div");
  wrap.className = "tile-bamboo";
  wrap.style.setProperty("--bam-cols", pattern.cols);
  pattern.colors.forEach(c => {
    wrap.appendChild(createBamSvgStick(c === "r" || c === "c", c === "c"));
  });
  return wrap;
}

function renderTile(tileCode, isPlayer = false) {
  const div = document.createElement("div");
  let baseClass = "tile";

  const suit = tileCode[0];
  const val = parseInt(tileCode.slice(1), 10);

  const flowerNames = ["春", "夏", "秋", "冬", "梅", "蘭", "竹", "菊",
                       "琴", "棋", "書", "畫", "貓", "雞", "蟲", "鼠"];
  const chineseNums  = ["一","二","三","四","五","六","七","八","九"];

  const suitLabel =
    suit === "M" ? "萬" :
    suit === "P" ? "筒" :
    suit === "S" ? "條" :
    suit === "F" ? "花" :
    "";

  if (suit === "M") baseClass += " man";
  else if (suit === "P") baseClass += " pin";
  else if (suit === "S") baseClass += " sou";
  else if (suit === "Z") baseClass += " zi";
  else if (suit === "F") baseClass += " flower";
  else if (suit === "H") baseClass += " fei";

  if (isPlayer) baseClass += " player";
  div.className = baseClass;

  let valueLabel;
  if (suit === "Z") {
    valueLabel = ["東", "南", "西", "北", "中", "發", "白"][val - 1] || "?";
    // 東(Z1)南(Z2)西(Z3)北(Z4)全黑；中(Z5)紅；發(Z6)綠；白(Z7)特殊
    const ziColor = ["zi-dark","zi-dark","zi-dark","zi-dark","zi-red","zi-green","zi-white"];
    div.classList.add(ziColor[val - 1] || "zi-dark");
  } else if (suit === "F") {
    valueLabel = flowerNames[val - 1] || "?";
  } else if (suit === "H") {
    valueLabel = "飛";
  } else {
    valueLabel = chineseNums[val - 1] || String(val);
  }

  if (suit === "F") {
    // 花牌：左上號碼 + 右上名稱 + 中央 SVG 插圖
    const groupNum = ((val - 1) % 4) + 1;
    const isAnimal = val >= 13; // 貓雞蟲鼠：無號碼無文字
    const isSeason = val <= 4;  // 春夏秋冬用紅色
    if (!isAnimal) {
      const topRow = document.createElement("div");
      topRow.className = "flower-top";
      const numEl = document.createElement("span");
      numEl.className = "flower-num" + (isSeason ? " flower-red" : "");
      numEl.textContent = String(groupNum);
      topRow.appendChild(numEl);
      const nameEl = document.createElement("span");
      nameEl.className = "flower-name" + (isSeason ? " flower-red" : "");
      nameEl.textContent = valueLabel;
      topRow.appendChild(nameEl);
      div.appendChild(topRow);
    }
    const artEl = document.createElement("div");
    artEl.className = "flower-art" + (isAnimal ? " flower-art-full" : "");
    artEl.appendChild(createFlowerSvg(val));
    div.appendChild(artEl);
  } else if (suit === "Z" && val === 7) {
    // 白板：同心圓角方框 SVG
    div.appendChild(createBaiSvg());
  } else if (suit === "P") {
    // 筒牌：圓點陣列（無角落數字）
    div.appendChild(createPinDots(val));
  } else if (suit === "S") {
    // 條牌：竹節棒（無角落數字）
    div.appendChild(createBambooSticks(val));
  } else if (suit === "M") {
    // 萬牌：大黑數字上方 + 大紅「萬」下方，無角落字
    const valueEl = document.createElement("div");
    valueEl.className = "tile-value man-value";
    valueEl.textContent = valueLabel;
    div.appendChild(valueEl);
    const suitEl = document.createElement("div");
    suitEl.className = "tile-suit man-suit";
    suitEl.textContent = "萬";
    div.appendChild(suitEl);
  } else if (suit !== "F" && !(suit === "Z" && val === 7)) {
    // 字 / 飛：文字呈現（白板和花牌已由 SVG 處理，跳過）
    if (suitLabel) {
      const cornerEl = document.createElement("div");
      cornerEl.className = "tile-corner";
      cornerEl.textContent = valueLabel;
      div.appendChild(cornerEl);
    }
    const valueEl = document.createElement("div");
    valueEl.className = "tile-value";
    valueEl.textContent = valueLabel;
    div.appendChild(valueEl);
    if (suitLabel) {
      const suitEl = document.createElement("div");
      suitEl.className = "tile-suit";
      suitEl.textContent = suitLabel;
      div.appendChild(suitEl);
    }
  }

  return div;
}

function renderAiHand(container, count) {
  container.innerHTML = "";
  for (let i = 0; i < count; i++) {
    const div = document.createElement("div");
    div.className = "tile back";
    container.appendChild(div);
  }
}

function renderDiscardRow(container, tiles, playerIdx) {
  container.innerHTML = "";
  tiles.forEach((t, i) => {
    const el = renderTile(t, false);
    el.classList.add("discarded");
    // 最後一張且是當前 lastDiscard 來源 → 高亮
    if (lastDiscard && playerIdx !== undefined &&
        lastDiscard.from === playerIdx && i === tiles.length - 1) {
      el.classList.add("active-discard");
    }
    container.appendChild(el);
  });
}

function renderFlowersRow(container, tiles) {
  container.innerHTML = "";
  tiles.forEach((t) => {
    container.appendChild(renderTile(t, true));
  });
}

function renderMeldsRow(container, meldList) {
  if (!container) return;
  container.innerHTML = "";
  meldList.forEach((m) => {
    const wrap = document.createElement("div");
    wrap.className = "meld";
    m.tiles.forEach((t) => {
      wrap.appendChild(renderTile(t, false));
    });
    container.appendChild(wrap);
  });
}

// ── 骰子決庄家（三人版）──────────────────────────────────────────

function startNewGame() {
  showDiceOverlay();
}

function showDiceOverlay() {
  const overlay  = document.getElementById("dice-overlay");
  const resultEl = document.getElementById("dice-result-text");
  const die1El   = document.getElementById("die1");
  const die2El   = document.getElementById("die2");
  const rollBtn  = document.getElementById("btn-roll-dice");

  resultEl.innerHTML = "";
  die1El.textContent = DIE_CHARS[1]; // 顯示初始骰面
  die2El.textContent = DIE_CHARS[3];
  die1El.classList.remove("rolling");
  die2El.classList.remove("rolling");
  rollBtn.textContent = "擲骰子";
  rollBtn.disabled = false;
  rollBtn.onclick = startRolling;
  overlay.classList.remove("hidden");
}

function startRolling() {
  const die1El   = document.getElementById("die1");
  const die2El   = document.getElementById("die2");
  const resultEl = document.getElementById("dice-result-text");
  const rollBtn  = document.getElementById("btn-roll-dice");

  rollBtn.disabled = true;
  resultEl.innerHTML = "";
  die1El.classList.add("rolling");
  die2El.classList.add("rolling");

  let ticks = 0;
  const totalTicks = 22;

  const iv = setInterval(() => {
    die1El.textContent = DIE_CHARS[Math.floor(Math.random() * 6)];
    die2El.textContent = DIE_CHARS[Math.floor(Math.random() * 6)];
    ticks++;

    if (ticks >= totalTicks) {
      clearInterval(iv);
      die1El.classList.remove("rolling");
      die2El.classList.remove("rolling");

      const v1 = Math.floor(Math.random() * 6) + 1;
      const v2 = Math.floor(Math.random() * 6) + 1;
      die1El.textContent = DIE_CHARS[v1 - 1];
      die2El.textContent = DIE_CHARS[v2 - 1];

      const sum = v1 + v2;
      // 三人版：以點數和 mod 3 對應座位（南·東·西）
      const east = DICE_SEAT_ORDER[(sum - 2) % 3];
      const eastLabel = SEAT_NAMES_FULL[east];

      const isHuman = east === PLAYER_SOUTH;
      const icon = isHuman ? "🧑" : "🤖";
      resultEl.innerHTML =
        `擲出 <strong>${v1} ＋ ${v2} ＝ ${sum}</strong><br>` +
        `<span class="dice-east-badge">${icon} ${eastLabel}<br>成為本局庄家，優先出牌！</span>`;

      rollBtn.textContent = "開始遊戲";
      rollBtn.disabled = false;
      rollBtn.onclick = () => {
        // 讀取選中賠率
        const activeRate = document.querySelector(".rate-btn.active");
        if (activeRate) BASE_UNIT = parseInt(activeRate.dataset.rate, 10);
        document.getElementById("dice-overlay").classList.add("hidden");
        actuallyStartGame(east);
      };
    }
  }, 80);
}

function actuallyStartGame(east) {
  elLog.innerHTML = "";
  log("開始新的一局（三人麻將，16 張，無北風）", "system");
  resetState();
  dealerPlayer = east; // resetState 後再設定，避免被覆蓋
  currentTurn  = east; // 庄家先手
  dealInitialHands();
  render();
  log(`${SEAT_NAMES_FULL[east]} 成為本局庄家，先手出牌。`, "system");

  if (east === PLAYER_SOUTH) {
    setTimeout(onPlayerDraw, 400);
  } else {
    setTimeout(aiTakeTurn, 1200);
  }
}

function onPlayerDraw() {
  if (gameOver || currentTurn !== PLAYER_SOUTH || drawnThisTurn) return;
  if (wall.length === 0) {
    endGameDraw();
    return;
  }
  const tile = drawOneTileToHandOrFlower(PLAYER_SOUTH);
  if (!tile) {
    endGameDraw();
    return;
  }
  drawnThisTurn = true;
  afterKongDraw = false; // 普通摸牌，非嶺上
  turnCount++;
  log(`你摸了一張牌。`, "player");
  render();
}

function onPlayerDiscard(tile) {
  if (gameOver || currentTurn !== PLAYER_SOUTH || !drawnThisTurn) {
    if (!gameOver && currentTurn === PLAYER_SOUTH && !drawnThisTurn) {
      log("請先摸牌再打牌。", "warning");
    }
    return;
  }
  // 飛牌不可打出（萬用牌必須留在手中）
  if (tile[0] === "H") {
    log("飛牌不可打出，請打出其他牌。", "warning");
    return;
  }
  clearRecommend(); // 棄牌後清除推薦高亮
  const idx = hands[PLAYER_SOUTH].indexOf(tile);
  if (idx === -1) return;
  hands[PLAYER_SOUTH].splice(idx, 1);
  discards[PLAYER_SOUTH].push(tile);
  log(`你打出了：${formatTileLabel(tile)}`, "player");
  speakTile(tile);
  lastDiscard = { tile, from: PLAYER_SOUTH };
  // 打牌後自動排列（飛牌保持在最後）
  hands[PLAYER_SOUTH] = MJ.sortHand(hands[PLAYER_SOUTH]);
  endTurnAndNext();
}

function onPlayerWinAttempt() {
  if (gameOver || currentTurn !== PLAYER_SOUTH) return;

  // 榮胡：對別人打出的牌宣胡
  if (awaitingPlayerClaim && lastDiscard) {
    const winTile = lastDiscard.tile;
    if (MJ.isWinningHand([...hands[PLAYER_SOUTH], winTile])) {
      showActionOverlay("胡");
      log(`恭喜！你榮胡了！（胡 ${formatTileLabel(winTile)}）本局結束。`, "player");
      gameOver = true;
      awaitingPlayerClaim = false;
      render();
      showWinOverlay(PLAYER_SOUTH, { winTile, isRonghu: true });
      return;
    }
  }

  // 自摸胡
  const tiles = hands[PLAYER_SOUTH].slice();
  if (MJ.isWinningHand(tiles)) {
    showActionOverlay("胡");
    const kongWin = afterKongDraw;
    log(kongWin ? "恭喜！嶺上開花！本局結束。" : "恭喜！你自摸胡牌！本局結束。", "player");
    gameOver = true;
    render();
    showWinOverlay(PLAYER_SOUTH, { afterKong: kongWin });
  } else {
    log("目前牌型尚未符合胡牌（簡化檢查不通過）。", "warning");
  }
}

/* ── 輪轉輔助（三人版：南→西→東→南 循環）─────────────────────── */
function getNextPlayer(player) {
  if (player === PLAYER_SOUTH) return AI_WEST;
  if (player === AI_WEST)      return AI_EAST;
  return PLAYER_SOUTH; // AI_EAST → PLAYER_SOUTH
}

// 檢查 AI 是否能吃某張牌（順子，僅限數牌）
function canAiChi(ai, tile) {
  const suit = tile[0];
  const v = parseInt(tile.slice(1), 10);
  if (suit === "Z" || suit === "F" || suit === "H") return false;
  const has = (val) => hands[ai].some(t => t === `${suit}${val}`);
  return (v >= 3 && has(v - 2) && has(v - 1)) ||
         (v >= 2 && v <= 8 && has(v - 1) && has(v + 1)) ||
         (v <= 7 && has(v + 1) && has(v + 2));
}

// ── AI 搶牌後打牌（共用，延遲執行讓碰/吃/槓先渲染） ──────────────
function aiDiscardAfterClaim(ai) {
  if (gameOver) return;
  const discard = chooseAiDiscardByDifficulty(hands[ai]);
  const idx = hands[ai].indexOf(discard);
  if (idx !== -1) {
    hands[ai].splice(idx, 1);
    discards[ai].push(discard);
    log(`${getSeatName(ai)}打出了：${formatTileLabel(discard)}`, "ai");
    speakTile(discard);
    lastDiscard = { tile: discard, from: ai };
  }
  render();
  endTurnAndNext();
}

// ── AI 搶牌動作 ──────────────────────────────────────────────────
function aiClaimPeng(ai, tile, from) {
  if (gameOver) return;
  let removed = 0;
  for (let i = hands[ai].length - 1; i >= 0 && removed < 2; i--) {
    if (hands[ai][i] === tile) { hands[ai].splice(i, 1); removed++; }
  }
  const fromArr = discards[from];
  if (fromArr && fromArr[fromArr.length - 1] === tile) fromArr.pop();
  melds[ai].push({ type: "peng", tiles: [tile, tile, tile], from });
  showActionOverlay("碰");
  log(`${getSeatName(ai)} 碰了 ${getSeatName(from)} 打出的 ${formatTileLabel(tile)}`, "claim");
  currentTurn = ai;
  lastDiscard = null;
  render(); // 先渲染碰牌
  setTimeout(() => aiDiscardAfterClaim(ai), 900); // 延遲後再打牌
}

function aiClaimGang(ai, tile, from) {
  if (gameOver) return;
  let removed = 0;
  for (let i = hands[ai].length - 1; i >= 0 && removed < 3; i--) {
    if (hands[ai][i] === tile) { hands[ai].splice(i, 1); removed++; }
  }
  const fromArr = discards[from];
  if (fromArr && fromArr[fromArr.length - 1] === tile) fromArr.pop();
  melds[ai].push({ type: "gang", tiles: [tile, tile, tile, tile], from });
  showActionOverlay("槓");
  log(`${getSeatName(ai)} 明槓了 ${getSeatName(from)} 打出的 ${formatTileLabel(tile)}，補一張。`, "claim");
  currentTurn = ai;
  lastDiscard = null;
  afterKongDraw = true;
  render(); // 先渲染槓牌
  setTimeout(() => {
    if (gameOver) return;
    const newTile = drawOneTileToHandOrFlower(ai);
    if (!newTile) { endGameDraw(); return; }
    if (MJ.isWinningHand(hands[ai])) {
      showActionOverlay("胡");
      log(`${getSeatName(ai)} 嶺上開花！本局結束。`, "ai");
      gameOver = true;
      render();
      showWinOverlay(ai, { afterKong: true });
      return;
    }
    render(); // 渲染補牌
    setTimeout(() => aiDiscardAfterClaim(ai), 900); // 再延遲後打牌
  }, 900);
}

function aiClaimChi(ai, tile, from) {
  if (gameOver) return;
  const suit = tile[0];
  const v = parseInt(tile.slice(1), 10);
  const has = (val) => hands[ai].some(t => t === `${suit}${val}`);
  const removeTile = (code) => {
    const i = hands[ai].indexOf(code);
    if (i !== -1) hands[ai].splice(i, 1);
  };
  let meldTiles = null;
  if (v >= 3 && has(v - 2) && has(v - 1)) {
    meldTiles = [`${suit}${v - 2}`, `${suit}${v - 1}`, tile];
    removeTile(`${suit}${v - 2}`); removeTile(`${suit}${v - 1}`);
  } else if (v >= 2 && v <= 8 && has(v - 1) && has(v + 1)) {
    meldTiles = [`${suit}${v - 1}`, tile, `${suit}${v + 1}`];
    removeTile(`${suit}${v - 1}`); removeTile(`${suit}${v + 1}`);
  } else if (v <= 7 && has(v + 1) && has(v + 2)) {
    meldTiles = [tile, `${suit}${v + 1}`, `${suit}${v + 2}`];
    removeTile(`${suit}${v + 1}`); removeTile(`${suit}${v + 2}`);
  }
  if (!meldTiles) return;
  const fromArr = discards[from];
  if (fromArr && fromArr[fromArr.length - 1] === tile) fromArr.pop();
  melds[ai].push({ type: "chi", tiles: meldTiles, from });
  showActionOverlay("吃");
  log(`${getSeatName(ai)} 吃了 ${getSeatName(from)} 打出的 ${formatTileLabel(tile)}`, "claim");
  currentTurn = ai;
  lastDiscard = null;
  render(); // 先渲染吃牌
  setTimeout(() => aiDiscardAfterClaim(ai), 900); // 延遲後再打牌
}

// 搶牌：胡 > 槓 > 碰（三人版無吃；胡由 endTurnAndNext Phase1 統一處理）
function tryAiClaims(tile, from, startFrom) {
  let check = startFrom;
  for (let i = 0; i < 2; i++) { // 三人版：只有2個AI
    if (check !== PLAYER_SOUTH && check !== from) {
      if (MJ.isWinningHand([...hands[check], tile])) {
        const ai = check;
        setTimeout(() => {
          showActionOverlay("胡");
          log(`${getSeatName(ai)}榮胡！（胡 ${formatTileLabel(tile)}）本局結束。`, "ai");
          gameOver = true;
          render();
          showWinOverlay(ai, { winTile: tile, isRonghu: true });
        }, 350);
        return true;
      }
      if (hands[check].filter(t => t === tile).length >= 3 && aiShouldClaim("gang")) {
        const ai = check;
        setTimeout(() => aiClaimGang(ai, tile, from), 900);
        return true;
      }
      if (hands[check].filter(t => t === tile).length >= 2 && aiShouldClaim("peng")) {
        const ai = check;
        setTimeout(() => aiClaimPeng(ai, tile, from), 900);
        return true;
      }
    }
    check = getNextPlayer(check);
  }
  return false;
}

// 只處理 AI 槓/碰（三人版無吃；兩輪掃描：槓 > 碰）
function tryAiClaimsNonRong(tile, from, startFrom) {
  // 第一輪：找可槓的 AI
  let check = startFrom;
  for (let i = 0; i < 2; i++) {
    if (check !== PLAYER_SOUTH && check !== from) {
      if (hands[check].filter(t => t === tile).length >= 3 && aiShouldClaim("gang")) {
        const ai = check;
        setTimeout(() => aiClaimGang(ai, tile, from), 900);
        return true;
      }
    }
    check = getNextPlayer(check);
  }
  // 第二輪：無人可槓，找可碰的 AI
  check = startFrom;
  for (let i = 0; i < 2; i++) {
    if (check !== PLAYER_SOUTH && check !== from) {
      if (hands[check].filter(t => t === tile).length >= 2 && aiShouldClaim("peng")) {
        const ai = check;
        setTimeout(() => aiClaimPeng(ai, tile, from), 900);
        return true;
      }
    }
    check = getNextPlayer(check);
  }
  return false;
}

/* ── 跨玩家搶牌優先級（三人版：只有2個AI，槓 > 碰 > 胡 優先）── */
function anyAiCanGang(tile, from, startFrom) {
  let check = startFrom;
  for (let i = 0; i < 2; i++) {
    if (check !== PLAYER_SOUTH && check !== from) {
      if (hands[check].filter(t => t === tile).length >= 3) return true;
    }
    check = getNextPlayer(check);
  }
  return false;
}
function anyAiCanPeng(tile, from, startFrom) {
  let check = startFrom;
  for (let i = 0; i < 2; i++) {
    if (check !== PLAYER_SOUTH && check !== from) {
      if (hands[check].filter(t => t === tile).length >= 2) return true;
    }
    check = getNextPlayer(check);
  }
  return false;
}

function endTurnAndNext() {
  drawnThisTurn = false;
  render();
  if (wall.length === 0) { endGameDraw(); return; }
  if (gameOver) return;

  if (lastDiscard) {
    const tile = lastDiscard.tile;
    const from = lastDiscard.from;
    const naturalNext = getNextPlayer(from);

    if (from !== PLAYER_SOUTH) {
      // ── Phase 1：胡 優先，全場掃描（玩家 → AI 依序） ──────────────
      const playerCanRong =
        (hands[PLAYER_SOUTH].length + 1) % 3 === 2 &&
        MJ.isWinningHand([...hands[PLAYER_SOUTH], tile]);

      // 找第一個可榮胡的 AI（按出牌後的輪轉順序）
      let aiRongWinner = null;
      let chk = naturalNext;
      for (let i = 0; i < 2; i++) { // 三人版：只有2個AI
        if (chk !== PLAYER_SOUTH && chk !== from &&
            MJ.isWinningHand([...hands[chk], tile])) {
          aiRongWinner = chk;
          break;
        }
        chk = getNextPlayer(chk);
      }

      if (playerCanRong) {
        // 玩家可胡：只顯示胡按鈕，不顯示碰/吃/槓
        claimOptions = { chi: false, peng: false, gang: false, chiOptions: [] };
        awaitingPlayerClaim = true;
        currentTurn = PLAYER_SOUTH;
        pendingTurnAfterDiscard = naturalNext;
        log(`你可以對 ${getSeatName(from)} 的牌（${formatTileLabel(tile)}）做動作。`, "system");
        render();
        return;
      }

      if (aiRongWinner !== null) {
        // AI 可胡：直接宣告，任何人都不能碰/吃/槓
        const ai = aiRongWinner;
        setTimeout(() => {
          showActionOverlay("胡");
          log(`${getSeatName(ai)}榮胡！（胡 ${formatTileLabel(tile)}）本局結束。`, "ai");
          gameOver = true;
          render();
          showWinOverlay(ai, { winTile: tile, isRonghu: true });
        }, 350);
        return;
      }

      // ── Phase 2–3：嚴格全場優先 槓 > 碰（三人版無吃）────────────────
      computePlayerClaimOptions();

      const playerCanGang = claimOptions.gang;
      const playerCanPeng = claimOptions.peng;
      const aiGang = anyAiCanGang(tile, from, naturalNext);
      const aiPeng = anyAiCanPeng(tile, from, naturalNext);

      // 槓 優先：玩家可槓
      if (playerCanGang) {
        claimOptions = { chi: false, peng: false, gang: true, chiOptions: [] };
        awaitingPlayerClaim = true;
        currentTurn = PLAYER_SOUTH;
        pendingTurnAfterDiscard = naturalNext;
        log(`你可以對 ${getSeatName(from)} 的牌（${formatTileLabel(tile)}）做動作。`, "system");
        render();
        return;
      }
      // 槓 優先：AI 可槓
      if (aiGang) {
        awaitingPlayerClaim = false;
        claimOptions = { chi: false, peng: false, gang: false, chiOptions: [] };
      }
      // 碰 優先（無人可槓）：玩家可碰
      else if (playerCanPeng) {
        claimOptions = { chi: false, peng: true, gang: false, chiOptions: [] };
        awaitingPlayerClaim = true;
        currentTurn = PLAYER_SOUTH;
        pendingTurnAfterDiscard = naturalNext;
        log(`你可以對 ${getSeatName(from)} 的牌（${formatTileLabel(tile)}）做動作。`, "system");
        render();
        return;
      }
      // 碰 優先：AI 可碰
      else if (aiPeng) {
        awaitingPlayerClaim = false;
        claimOptions = { chi: false, peng: false, gang: false, chiOptions: [] };
      }
      // 三人版：無吃牌，直接進入下家
    }

    // ── Phase 3：AI 槓/碰（兩輪掃描，槓 > 碰）────────────────────────
    if (tryAiClaimsNonRong(tile, from, naturalNext)) return;

    // 三人版：無吃牌（Phase 4 移除）

    // 無人搶牌，輪到自然下家
    currentTurn = naturalNext;
  } else {
    currentTurn = getNextPlayer(currentTurn);
  }

  render();
  if (!gameOver) {
    if (currentTurn !== PLAYER_SOUTH) {
      setTimeout(aiTakeTurn, 1000);
    } else {
      setTimeout(onPlayerDraw, 400);
    }
  }
}

function aiTakeTurn() {
  if (gameOver) return;

  if (wall.length === 0) {
    endGameDraw();
    return;
  }

  // AI 摸牌
  const tile = drawOneTileToHandOrFlower(currentTurn);
  if (!tile) {
    endGameDraw();
    return;
  }
  log(`${getSeatName(currentTurn)}摸了一張牌。`, "ai");
  afterKongDraw = false; // AI 普通摸牌，重置嶺上旗標
  turnCount++;

  // AI 嘗試自摸胡
  if (MJ.isWinningHand(hands[currentTurn])) {
    showActionOverlay("胡");
    log(`${getSeatName(currentTurn)}自摸胡牌！`, "ai");
    gameOver = true;
    render();
    showWinOverlay(currentTurn);
    return;
  }

  const discard = chooseAiDiscardByDifficulty(hands[currentTurn]);
  const idx = hands[currentTurn].indexOf(discard);
  if (idx !== -1) {
    hands[currentTurn].splice(idx, 1);
    if (discard[0] === "H") {
      feis[currentTurn].push(discard);
      log(`${getSeatName(currentTurn)}打出飛牌。`, "ai");
      speakTile(discard);
      lastDiscard = null;
    } else {
      discards[currentTurn].push(discard);
      log(`${getSeatName(currentTurn)}打出了：${formatTileLabel(discard)}`, "ai");
      speakTile(discard);
      lastDiscard = { tile: discard, from: currentTurn };
    }
  }

  endTurnAndNext();
}

// 三人麻將：無吃牌，只計算碰/槓/胡
function computePlayerClaimOptions() {
  awaitingPlayerClaim = false;
  claimOptions = { chi: false, peng: false, gang: false, chiOptions: [] };
  if (!lastDiscard) return;
  const tile = lastDiscard.tile;
  const feiCount = hands[PLAYER_SOUTH].filter((t) => t[0] === "H").length;

  // 碰：手牌中有兩張同樣的牌（或搭配飛牌）
  const sameCount = hands[PLAYER_SOUTH].filter((t) => t === tile).length;
  const canPeng = sameCount >= 2 || (sameCount >= 1 && feiCount >= 1) || (tile[0] === "H" && feiCount >= 2);
  if (canPeng) claimOptions.peng = true;

  // 槓：手牌有3張相同（飛牌不能用於槓）
  if (sameCount >= 3) claimOptions.gang = true;

  // 三人版：無吃牌 (claimOptions.chi 保持 false)

  awaitingPlayerClaim = claimOptions.peng || claimOptions.gang;

  // 能胡時，清空碰/槓選項，保持 awaitingPlayerClaim = true 讓胡按鈕顯示
  if (lastDiscard) {
    const t = lastDiscard.tile;
    const canRonghu =
      (hands[PLAYER_SOUTH].length + 1) % 3 === 2 &&
      MJ.isWinningHand([...hands[PLAYER_SOUTH], t]);
    if (canRonghu) {
      claimOptions = { chi: false, peng: false, gang: false, chiOptions: [] };
      awaitingPlayerClaim = true;
    }
  }
}

function onPlayerPass() {
  if (!awaitingPlayerClaim || gameOver) return;
  awaitingPlayerClaim = false;
  claimOptions = { chi: false, peng: false, gang: false, chiOptions: [] };

  const tile = lastDiscard ? lastDiscard.tile : null;
  const from = lastDiscard ? lastDiscard.from : null;
  const nextPlayer = pendingTurnAfterDiscard || getNextPlayer(currentTurn);
  pendingTurnAfterDiscard = null;
  render();

  if (tile && from) {
    // 玩家過後，AI 仍可搶牌（胡/槓/碰）；三人版無吃
    if (tryAiClaims(tile, from, getNextPlayer(from))) return;
  }

  // 無 AI 搶牌，繼續輪到自然下家
  currentTurn = nextPlayer;
  lastDiscard = null;
  render();
  if (!gameOver) {
    if (currentTurn !== PLAYER_SOUTH) {
      setTimeout(aiTakeTurn, 1000);
    } else {
      setTimeout(onPlayerDraw, 400);
    }
  }
}

function onPlayerPeng() {
  if (!awaitingPlayerClaim || !claimOptions.peng || !lastDiscard) return;
  const tile = lastDiscard.tile;

  // 從手牌取出 2 張（優先真實牌，不足才用飛）
  let need = 2;
  const handTilesUsed = [];
  for (let i = hands[PLAYER_SOUTH].length - 1; i >= 0 && need > 0; i--) {
    if (hands[PLAYER_SOUTH][i] === tile) {
      hands[PLAYER_SOUTH].splice(i, 1);
      handTilesUsed.push(tile);
      need--;
    }
  }
  for (let i = hands[PLAYER_SOUTH].length - 1; i >= 0 && need > 0; i--) {
    if (hands[PLAYER_SOUTH][i][0] === "H") {
      handTilesUsed.push(hands[PLAYER_SOUTH].splice(i, 1)[0]);
      need--;
    }
  }

  const fromArr = discards[lastDiscard.from];
  if (fromArr && fromArr[fromArr.length - 1] === tile) {
    fromArr.pop();
  } else if (tile[0] === "H") {
    const feiArr = feis[lastDiscard.from];
    if (feiArr && feiArr.length > 0) feiArr.pop();
  }
  showActionOverlay("碰");
  log(`你碰了 ${getSeatName(lastDiscard.from)} 打出的 ${formatTileLabel(tile)}，請打出一張牌。`, "claim");

  // 建立面子：手牌用的 2 張 + 搶的棄牌 1 張
  const meldTiles = [...handTilesUsed, tile];
  const feiSubs = [];
  handTilesUsed.forEach((t, i) => {
    if (t[0] === "H") feiSubs.push({ pos: i, feiTile: t, subFor: tile });
  });
  melds[PLAYER_SOUTH].push({
    type: "peng",
    tiles: meldTiles,
    from: lastDiscard.from,
    feiSubs,
  });
  awaitingPlayerClaim = false;
  claimOptions = { chi: false, peng: false, gang: false, chiOptions: [] };
  currentTurn = PLAYER_SOUTH;
  drawnThisTurn = true; // 直接允許你打牌
  lastDiscard = null;
  render();
}

function onPlayerGang() {
  // 1. 明槓：對別人的棄牌（飛牌不可用於槓）
  if (awaitingPlayerClaim && claimOptions.gang && lastDiscard) {
    const tile = lastDiscard.tile;
    let need = 3;
    for (let i = hands[PLAYER_SOUTH].length - 1; i >= 0 && need > 0; i--) {
      if (hands[PLAYER_SOUTH][i] === tile) {
        hands[PLAYER_SOUTH].splice(i, 1);
        need--;
      }
    }
    const fromArr = discards[lastDiscard.from];
    if (fromArr && fromArr[fromArr.length - 1] === tile) {
      fromArr.pop();
    } else if (tile[0] === "H") {
      const feiArr = feis[lastDiscard.from];
      if (feiArr && feiArr.length > 0) feiArr.pop();
    }
    melds[PLAYER_SOUTH].push({
      type: "gang",
      tiles: [tile, tile, tile, tile],
      from: lastDiscard.from,
    });
    showActionOverlay("槓");
    log(`你明槓了 ${getSeatName(lastDiscard.from)} 打出的 ${formatTileLabel(tile)}，補一張牌。`, "claim");
    awaitingPlayerClaim = false;
    claimOptions = { chi: false, peng: false, gang: false, chiOptions: [] };
    currentTurn = PLAYER_SOUTH;
    lastDiscard = null;
    // 槓後補牌（嶺上開花）
    drawnThisTurn = false;
    afterKongDraw = true;
    onPlayerDraw();
    return;
  }

  // 2. 加槓：手中有牌與已碰面子相同，升級為槓
  if (!awaitingPlayerClaim && currentTurn === PLAYER_SOUTH && drawnThisTurn) {
    const addTile = findAddKongTile();
    if (addTile) {
      const idx = hands[PLAYER_SOUTH].indexOf(addTile);
      hands[PLAYER_SOUTH].splice(idx, 1);
      const meld = melds[PLAYER_SOUTH].find(m => m.type === "peng" &&
        m.tiles.find(t => t[0] !== "H") === addTile);
      if (meld) {
        meld.tiles.push(addTile);
        meld.type = "gang";
      }
      showActionOverlay("槓");
      log(`你加槓了 ${formatTileLabel(addTile)}（自己的碰牌升級），補一張牌。`, "claim");
      drawnThisTurn = false;
      afterKongDraw = true;
      onPlayerDraw();
      return;
    }
  }

  // 3. 暗槓：自摸 4 張完全相同（飛牌不可替代）
  if (!awaitingPlayerClaim && currentTurn === PLAYER_SOUTH && drawnThisTurn) {
    const tile = findConcealedGangTile();
    if (!tile) return;
    let removed = 0;
    for (let i = hands[PLAYER_SOUTH].length - 1; i >= 0 && removed < 4; i--) {
      if (hands[PLAYER_SOUTH][i] === tile) {
        hands[PLAYER_SOUTH].splice(i, 1);
        removed++;
      }
    }
    melds[PLAYER_SOUTH].push({
      type: "gang",
      tiles: [tile, tile, tile, tile],
      from: PLAYER_SOUTH,
      concealed: true,
    });
    showActionOverlay("槓");
    log(`你暗槓了 ${formatTileLabel(tile)}（四張在手），補一張牌。`, "claim");
    drawnThisTurn = false;
    onPlayerDraw();
  }
}

// 顯示吃牌選擇器（三人版無吃，此函數不會被呼叫，僅保留以防萬一）
function showChiSelector(options, tile) {
  const overlay = document.getElementById("chi-select-overlay");
  const optsEl  = document.getElementById("chi-select-options");
  if (!overlay || !optsEl) return; // 三人版不存在此元素

  optsEl.innerHTML = "";
  options.forEach((pattern) => {
    const btn = document.createElement("div");
    btn.className = "chi-option-btn";
    pattern.forEach((t) => {
      const tileEl = renderTile(t, false);
      if (t === tile) tileEl.classList.add("discard-tile");
      btn.appendChild(tileEl);
    });
    btn.addEventListener("click", () => {
      overlay.classList.add("hidden");
      executeChiPattern(pattern, tile);
    });
    optsEl.appendChild(btn);
  });

  const cancelBtn = document.getElementById("btn-chi-cancel");
  if (cancelBtn) cancelBtn.onclick = () => { overlay.classList.add("hidden"); };
  overlay.classList.remove("hidden");
}

// 執行特定吃牌組合
function executeChiPattern(pattern, tile) {
  if (!lastDiscard) return;
  const meldTiles = [...pattern];
  const feiSubs   = [];

  for (let pos = 0; pos < pattern.length; pos++) {
    const t = pattern[pos];
    if (t === tile) continue; // 棄牌由對方貢獻，不從手牌移除

    const idx = hands[PLAYER_SOUTH].indexOf(t);
    if (idx !== -1) {
      hands[PLAYER_SOUTH].splice(idx, 1);
    } else {
      // 手牌沒有 → 用飛牌代替
      const feiIdx = hands[PLAYER_SOUTH].findIndex((x) => x[0] === "H");
      if (feiIdx === -1) return; // 不應發生（computePlayerClaimOptions 已驗證）
      const fei = hands[PLAYER_SOUTH].splice(feiIdx, 1)[0];
      meldTiles[pos] = fei;
      feiSubs.push({ pos, feiTile: fei, subFor: t });
    }
  }

  // 從棄牌堆移除該張牌
  const fromArr = discards[lastDiscard.from];
  if (fromArr && fromArr[fromArr.length - 1] === tile) fromArr.pop();

  finishChi(meldTiles, feiSubs, tile);
}

// 飛牌作為棄牌被吃（自動選第一個有效搭子）
function executeChiFei(tile) {
  if (!lastDiscard) return;
  const removeTile = (code) => {
    const idx = hands[PLAYER_SOUTH].indexOf(code);
    if (idx !== -1) { hands[PLAYER_SOUTH].splice(idx, 1); return true; }
    return false;
  };
  for (const s of ["M", "P", "S"]) {
    for (let vv = 1; vv <= 7; vv++) {
      const hHas = (val) => hands[PLAYER_SOUTH].includes(`${s}${val}`);
      const tryPair = (a, b) => {
        if (hHas(a) && hHas(b)) {
          removeTile(`${s}${a}`); removeTile(`${s}${b}`);
          return [`${s}${a}`, `${s}${b}`, tile];
        }
        return null;
      };
      const found = tryPair(vv, vv + 1) || tryPair(vv, vv + 2) || tryPair(vv + 1, vv + 2);
      if (found) {
        const feiArr = feis[lastDiscard.from];
        if (feiArr && feiArr.length > 0) feiArr.pop();
        finishChi(found, [], tile);
        return;
      }
    }
  }
}

function finishChi(meldTiles, feiSubs, tile) {
  showActionOverlay("吃");
  log(`你吃了 ${getSeatName(lastDiscard ? lastDiscard.from : PLAYER_SOUTH)} 打出的 ${formatTileLabel(tile)}，請打出一張牌。`, "claim");
  melds[PLAYER_SOUTH].push({
    type: "chi",
    tiles: meldTiles,
    from: lastDiscard.from,
    feiSubs,
  });
  awaitingPlayerClaim = false;
  claimOptions = { chi: false, peng: false, gang: false, chiOptions: [] };
  currentTurn = PLAYER_SOUTH;
  drawnThisTurn = true;
  lastDiscard = null;
  render();
}

function onPlayerChi() {
  if (!awaitingPlayerClaim || !claimOptions.chi || !lastDiscard) return;
  const tile = lastDiscard.tile;

  // 飛牌作為棄牌被吃 → 自動選第一個有效組合
  if (tile[0] === "H") {
    executeChiFei(tile);
    return;
  }

  // 一般牌：根據可選組合數決定是否顯示選擇器
  const opts = claimOptions.chiOptions || [];
  if (opts.length === 0) return;
  if (opts.length === 1) {
    executeChiPattern(opts[0], tile);
  } else {
    showChiSelector(opts, tile);
  }
}

function findConcealedGangTile() {
  const counts = {};
  for (const t of hands[PLAYER_SOUTH]) {
    if (t[0] !== "H") counts[t] = (counts[t] || 0) + 1;
  }
  for (const [tile, count] of Object.entries(counts)) {
    if (count >= 4) return tile;
  }
  return null;
}

// 加槓：摸到與已碰面子相同的牌（返回可加槓的牌，否則 null）
function findAddKongTile() {
  for (const meld of melds[PLAYER_SOUTH]) {
    if (meld.type !== "peng") continue;
    const realTile = meld.tiles.find(t => t[0] !== "H");
    if (!realTile) continue;
    if (hands[PLAYER_SOUTH].some(t => t === realTile)) return realTile;
  }
  return null;
}

/* ── 飛牌換回（換飛功能：將副露中的飛換成手牌中的真實牌）─────── */
// 若手牌中有牌可以替換某個面子裡的飛牌，回傳換牌資訊
function findFeiSwapOption() {
  for (const handTile of hands[PLAYER_SOUTH]) {
    for (let m = 0; m < melds[PLAYER_SOUTH].length; m++) {
      const meld = melds[PLAYER_SOUTH][m];
      if (!meld.feiSubs || meld.feiSubs.length === 0) continue;
      for (let f = 0; f < meld.feiSubs.length; f++) {
        if (meld.feiSubs[f].subFor === handTile) {
          return { handTile, meldIdx: m, feiSubIdx: f };
        }
      }
    }
  }
  return null;
}

function onSwapFei() {
  if (gameOver || !drawnThisTurn) return;
  const swap = findFeiSwapOption();
  if (!swap) return;
  const { handTile, meldIdx, feiSubIdx } = swap;
  const meld = melds[PLAYER_SOUTH][meldIdx];
  const { pos, feiTile } = meld.feiSubs[feiSubIdx];

  // 面子裡的飛牌換成真實牌
  meld.tiles[pos] = handTile;
  meld.feiSubs.splice(feiSubIdx, 1);

  // 手牌移除真實牌，補回飛牌
  const handIdx = hands[PLAYER_SOUTH].indexOf(handTile);
  hands[PLAYER_SOUTH].splice(handIdx, 1);
  hands[PLAYER_SOUTH].push(feiTile);
  hands[PLAYER_SOUTH] = MJ.sortHand(hands[PLAYER_SOUTH]);

  log(`你將面子中的飛換回手牌，${formatTileLabel(handTile)} 補入面子。`, "player");
  render();
}

function endGameDraw() {
  if (gameOver) return;
  log("牌山用盡，本局流局。", "system");
  gameOver = true;
  render();
  showDrawOverlay();
}

function showDrawOverlay() {
  const overlay   = document.getElementById("win-overlay");
  const nameEl    = document.getElementById("win-player-name");
  const typeEl    = document.getElementById("win-type");
  const yakuEl    = document.getElementById("win-yaku");
  const scoreEl   = document.getElementById("win-score");
  const allHands  = document.getElementById("win-all-hands");
  const noticeEl  = document.getElementById("bankrupt-notice");
  const closeBtn  = document.getElementById("btn-close-win");

  // 標題
  const titleEl = document.getElementById("win-title");
  if (titleEl) { titleEl.textContent = "流局！"; titleEl.classList.add("draw"); }
  nameEl.innerHTML = '<span class="game-avatar win-avatar">🀫</span> 牌山用盡';
  typeEl.textContent = "無人胡牌，本局流局";
  if (yakuEl)  yakuEl.innerHTML  = "";
  if (scoreEl) scoreEl.innerHTML = "";
  if (noticeEl) noticeEl.classList.add("hidden");
  if (closeBtn) closeBtn.textContent = "開始新局";

  // 顯示各家手牌
  if (allHands) {
    allHands.innerHTML = "";
    const DIR_LABEL  = { S: "南", E: "東", W: "西" };
    const SEAT_AVATAR = { S: playerAvatar, E: "🐯", W: "🦁" };
    [PLAYER_SOUTH, AI_EAST, AI_WEST].forEach(pid => {
      const row = document.createElement("div");
      row.className = "wah-row";

      const info = document.createElement("div");
      info.className = "wah-info";
      const av = document.createElement("span");
      av.className = "game-avatar wah-avatar";
      av.textContent = SEAT_AVATAR[pid] ?? "🀄";
      info.appendChild(av);
      const dir = document.createElement("span");
      dir.className = "wah-dir";
      dir.textContent = DIR_LABEL[pid] || "";
      info.appendChild(dir);
      const nm = document.createElement("span");
      nm.className = "wah-name";
      nm.textContent = pid === PLAYER_SOUTH ? playerName : getSeatName(pid).replace("人機 ", "AI");
      info.appendChild(nm);
      if (pid === dealerPlayer) {
        const db = document.createElement("span");
        db.className = "win-dealer-badge";
        db.textContent = "庄";
        info.appendChild(db);
      }
      row.appendChild(info);

      const tilesWrap = document.createElement("div");
      tilesWrap.className = "wah-tiles";
      // 副露
      (melds[pid] || []).forEach(meld => {
        const grp = document.createElement("div");
        grp.className = "wah-meld-group";
        meld.tiles.forEach(t => grp.appendChild(renderTile(t, false)));
        tilesWrap.appendChild(grp);
      });
      // 手牌
      const handGrp = document.createElement("div");
      handGrp.className = "wah-meld-group";
      MJ.sortHand(hands[pid]).forEach(t => handGrp.appendChild(renderTile(t, false)));
      tilesWrap.appendChild(handGrp);
      // 花牌
      const pidFlowers = flowers[pid] || [];
      if (pidFlowers.length > 0) {
        const sep = document.createElement("div");
        sep.className = "wah-sep";
        tilesWrap.appendChild(sep);
        pidFlowers.forEach(t => tilesWrap.appendChild(renderTile(t, false)));
      }
      row.appendChild(tilesWrap);
      allHands.appendChild(row);
    });
  }

  overlay.classList.remove("hidden");

  // 加入胡牌記錄（標記為流局）
  const now = new Date();
  const timeStr = `${String(now.getHours()).padStart(2,"0")}:${String(now.getMinutes()).padStart(2,"0")}`;
  winHistory.unshift({
    time:    timeStr,
    winner:  "流局",
    avatar:  "🀫",
    winType: "流局",
    fan:     0,
    payout:  0,
    isDealer: false,
  });
}

/* ══════════════════════════════════════════════════════════════
   工具函式（三人版）
   getSeatName() / speakTile() / formatTileLabel() / log()
   ══════════════════════════════════════════════════════════════ */
function getSeatName(id) {
  switch (id) {
    case PLAYER_SOUTH: return playerName;
    case AI_EAST:      return "人機 2";
    case AI_WEST:      return "人機 1";
    default:           return "人機";
  }
}

function speakTile(tileCode) {
  if (!window.speechSynthesis || allMuted) return;
  const nums = ["", "一", "二", "三", "四", "五", "六", "七", "八", "九"];
  const suit = tileCode[0];
  const v = parseInt(tileCode.slice(1), 10);
  const flowerNames = ["春", "夏", "秋", "冬", "梅", "蘭", "竹", "菊",
                       "琴", "棋", "書", "畫", "貓", "雞", "蟲", "鼠"];
  let text = "";
  if (suit === "M")      text = `${nums[v]}萬`;
  else if (suit === "P") text = `${nums[v]}筒`;
  else if (suit === "S") text = `${nums[v]}條`;
  else if (suit === "Z") text = (["東風", "南風", "西風", "北風", "紅中", "發財", "白板"][v - 1]) || "";
  else if (suit === "F") text = flowerNames[v - 1] || "";
  else if (suit === "H") text = "飛";
  if (!text) return;
  const utt = new SpeechSynthesisUtterance(text);
  utt.lang = "zh-TW";
  utt.rate = 1.1;
  window.speechSynthesis.cancel();
  window.speechSynthesis.speak(utt);
}

function formatTileLabel(tileCode) {
  const suit = tileCode[0];
  const v = parseInt(tileCode.slice(1), 10);
  const flowerNames = ["春", "夏", "秋", "冬", "梅", "蘭", "竹", "菊",
                       "琴", "棋", "書", "畫", "貓", "雞", "蟲", "鼠"];
  if (suit === "Z") {
    return ["東", "南", "西", "北", "中", "發", "白"][v - 1] || tileCode;
  }
  if (suit === "F") {
    return flowerNames[v - 1] || tileCode;
  }
  if (suit === "H") return "飛";
  const suitLabel =
    suit === "M" ? "萬" :
    suit === "P" ? "筒" :
    suit === "S" ? "條" :
    "";
  return `${v}${suitLabel}`;
}

// 初始渲染（不自動開局，等主頁點擊）
render();

// ── 訊息面板拖動 ──────────────────────────────────────────
(function initLogPanelDrag() {
  // 訊息面板固定右下角，不再支援拖拽
  const panel  = document.getElementById("log-panel");
  if (!panel) return;
  // 清除任何殘留的 inline style 位置
  panel.style.left   = "";
  panel.style.top    = "";
  panel.style.bottom = "";

  // 以下事件監聽器保留空函數佔位，不添加拖拽邏輯
  // (dragging logic removed)

  document.addEventListener("touchend", () => { dragging = false; });
})();

// ── 全部靜音控制（BGM + 語音） ────────────────────────────────────
(function initBgm() {
  const bgm       = document.getElementById("bgm");
  const btnToggle = document.getElementById("btn-bgm-toggle");
  const volSlider = document.getElementById("bgm-volume");
  if (!bgm || !btnToggle) return;

  // 讀取儲存的設定（預設：開啟，音量 0.4）
  let bgmEnabled = localStorage.getItem("bgm-enabled") !== "false";
  let volume     = parseFloat(localStorage.getItem("bgm-volume") ?? "0.4");

  bgm.volume = volume;
  if (volSlider) volSlider.value = volume;

  function updateUI() {
    btnToggle.textContent = allMuted ? "🔇 靜音" : "🔊 聲音";
    btnToggle.title = allMuted ? "點擊開啟聲音" : "點擊關閉聲音";
    btnToggle.classList.toggle("muted", allMuted);
    if (volSlider) volSlider.style.opacity = allMuted ? "0.35" : "1";
  }

  function tryPlay() {
    if (!bgmEnabled || allMuted) return;
    bgm.play().catch(() => {});
  }

  function applyMute() {
    if (allMuted) {
      bgm.pause();
      if (window.speechSynthesis) window.speechSynthesis.cancel();
    } else {
      if (bgmEnabled) tryPlay();
    }
  }

  // 第一次用戶互動時嘗試播放
  function onFirstInteraction() { tryPlay(); }
  document.addEventListener("click",      onFirstInteraction, { once: true });
  document.addEventListener("touchstart", onFirstInteraction, { once: true, passive: true });
  document.addEventListener("keydown",    onFirstInteraction, { once: true });

  // 同步主頁聲音按鈕 UI
  function syncHomeSound() {
    const homeToggle = document.getElementById("btn-home-sound-toggle");
    const homeIcon   = document.getElementById("home-sound-icon");
    const homeLabel  = document.getElementById("home-sound-label");
    const homeVol    = document.getElementById("home-bgm-volume");
    if (homeIcon)  homeIcon.textContent  = allMuted ? "🔇" : "🔊";
    if (homeLabel) homeLabel.textContent = allMuted ? "聲音：關" : "聲音：開";
    if (homeToggle) homeToggle.classList.toggle("muted", allMuted);
    if (homeVol) {
      homeVol.value   = volume;
      homeVol.style.opacity = allMuted ? "0.35" : "1";
    }
  }

  // 主頁聲音 toggle
  const homeToggleBtn = document.getElementById("btn-home-sound-toggle");
  if (homeToggleBtn) {
    homeToggleBtn.addEventListener("click", (e) => {
      e.stopPropagation();
      allMuted = !allMuted;
      localStorage.setItem("all-muted", allMuted);
      applyMute();
      updateUI();
      syncHomeSound();
    });
  }

  // 主頁音量滑桿
  const homeVolSlider = document.getElementById("home-bgm-volume");
  if (homeVolSlider) {
    homeVolSlider.value = volume;
    homeVolSlider.addEventListener("input", () => {
      volume = parseFloat(homeVolSlider.value);
      bgm.volume = volume;
      if (volSlider) volSlider.value = volume;
      localStorage.setItem("bgm-volume", volume);
      if (volume > 0 && !bgmEnabled) {
        bgmEnabled = true;
        localStorage.setItem("bgm-enabled", true);
      }
      if (!allMuted && bgmEnabled) tryPlay();
      updateUI();
      syncHomeSound();
    });
  }

  // 切換全部靜音
  btnToggle.addEventListener("click", (e) => {
    e.stopPropagation();
    allMuted = !allMuted;
    localStorage.setItem("all-muted", allMuted);
    applyMute();
    updateUI();
    syncHomeSound();
  });

  // 音量滑桿（僅控制 BGM 音量）
  if (volSlider) {
    volSlider.addEventListener("input", () => {
      volume = parseFloat(volSlider.value);
      bgm.volume = volume;
      localStorage.setItem("bgm-volume", volume);
      if (volume > 0 && !bgmEnabled) {
        bgmEnabled = true;
        localStorage.setItem("bgm-enabled", true);
      }
      if (!allMuted && bgmEnabled) tryPlay();
      updateUI();
    });
  }

  // 套用初始靜音狀態
  if (allMuted) applyMute();
  updateUI();
  syncHomeSound(); // 同步主頁音效按鈕狀態

  // 嘗試靜音 autoplay（部分瀏覽器允許），成功後恢復音量
  bgm.muted = true;
  bgm.play().then(() => {
    bgm.muted = false;
    bgm.volume = volume;
    if (!bgmEnabled || allMuted) bgm.pause();
  }).catch(() => {});
})();

// ── 鍵盤快捷鍵（方向鍵選牌 / P碰 / C吃 / H胡 / G槓 / D打牌 / Enter確認）──
document.addEventListener("keydown", (e) => {
  const tag = document.activeElement?.tagName;
  if (tag === "INPUT" || tag === "TEXTAREA") return;
  const overlayOpen = ["yaku-info-popup","game-preview-modal","win-detail-modal",
    "win-history-modal","tenpai-overlay","tile-ref-overlay","yaku-rules-overlay","avatar-picker"]
    .some(id => {
      const el = document.getElementById(id);
      if (!el) return false;
      return el.style.display !== "none" && !el.classList.contains("hidden");
    });
  if (overlayOpen) return;

  const isBtnActive = (btn) => btn && btn.style.display !== "none" && !btn.disabled;
  const hand = hands[PLAYER_SOUTH];

  switch (e.key) {
    case "ArrowLeft":
    case "ArrowUp": {
      if (!hand?.length || currentTurn !== PLAYER_SOUTH) return;
      e.preventDefault();
      kbdSelIdx = (kbdSelIdx <= 0) ? hand.length - 1 : kbdSelIdx - 1;
      applyKbdHighlight();
      break;
    }
    case "ArrowRight":
    case "ArrowDown": {
      if (!hand?.length || currentTurn !== PLAYER_SOUTH) return;
      e.preventDefault();
      kbdSelIdx = (kbdSelIdx < 0 || kbdSelIdx >= hand.length - 1) ? 0 : kbdSelIdx + 1;
      applyKbdHighlight();
      break;
    }
    case "Enter":
    case "d":
    case "D": {
      if (kbdSelIdx >= 0 && kbdSelIdx < (hand?.length ?? 0)) {
        e.preventDefault();
        const tile = hand[kbdSelIdx];
        kbdSelIdx = -1;
        applyKbdHighlight();
        onPlayerDiscard(tile);
      }
      break;
    }
    case "p":
    case "P":
      if (isBtnActive(btnPeng)) { e.preventDefault(); onPlayerPeng(); }
      break;
    case "c":
    case "C":
      if (btnChi && isBtnActive(btnChi)) { e.preventDefault(); onPlayerChi(); }
      break;
    case "h":
    case "H":
      if (isBtnActive(btnWin)) { e.preventDefault(); onPlayerWinAttempt(); }
      break;
    case "g":
    case "G":
      if (isBtnActive(btnGang)) { e.preventDefault(); onPlayerGang(); }
      break;
    case "t":
    case "T":
      if (isBtnActive(btnTenpai)) { e.preventDefault(); showTenpaiOverlay(); }
      break;
    case " ":
      if (isBtnActive(btnPass)) { e.preventDefault(); onPlayerPass(); }
      break;
    case "r":
    case "R":
      if (btnRecommend && btnRecommend.style.display !== "none") { e.preventDefault(); showRecommendation(); }
      break;
  }
});

// ── ESC 鍵關閉最頂層彈窗 ───────────────────────────────────────────
document.addEventListener("keydown", (e) => {
  if (e.key !== "Escape") return;
  const hide = (id, useDisplay) => {
    const el = document.getElementById(id);
    if (!el) return false;
    const visible = useDisplay
      ? el.style.display && el.style.display !== "none"
      : !el.classList.contains("hidden");
    if (!visible) return false;
    if (useDisplay) el.style.display = "none";
    else el.classList.add("hidden");
    return true;
  };
  if (hide("yaku-info-popup"))        return;
  if (hide("game-preview-modal"))     return;
  if (hide("win-detail-modal"))       return;
  if (hide("win-history-modal"))      return;
  if (hide("tenpai-overlay",   true)) return;
  if (hide("tile-ref-overlay", true)) return;
  if (hide("yaku-rules-overlay", true)) return;
  if (hide("tutorial-overlay", true)) return;
  if (hide("kbd-overlay",      true)) return;
  if (hide("avatar-picker"))          return;
  const menu = document.getElementById("game-menu-dropdown");
  if (menu && !menu.classList.contains("hidden")) { menu.classList.add("hidden"); return; }
  if (hide("recommend-overlay", true)) { clearRecommend(); return; }
});
