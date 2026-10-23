// ══════════════════════════════════════════════════════════════
// mahjong-core.js
// 麻將核心工具庫（由 mahjong4.js 使用）
//
// 功能：
//   1. createFullWall()  — 建立一副完整牌山（136 張 + 花牌 16 + 飛 4）
//   2. shuffle()         — Fisher-Yates 洗牌
//   3. sortHand()        — 依花色/點數排序手牌（僅用於顯示）
//   4. isWinningHand()   — 胡牌判斷（4副面子 + 1對將，支援飛萬用）
//   5. toCounts()        — 將牌陣列轉換為計數物件
//   6. canFormMelds()    — 無飛版面子分解
//   7. canFormMeldsWithFei() — 支援飛萬用的面子分解（遞迴回溯）
//   8. chooseAiDiscard() — 簡單 AI 棄牌策略（優先丟字牌/孤張）
//
// 所有函式掛載到 window.MJ 供其他腳本呼叫
// ══════════════════════════════════════════════════════════════

// 基本台灣 16 張牌庫與胡牌檢查（簡化版）

/* ── 花色常量 ── */
const SUIT_MAN = "M"; // 萬子（M1–M9）
const SUIT_PIN = "P"; // 筒子（P1–P9）
const SUIT_SOU = "S"; // 索子 / 條子（S1–S9）
const SUIT_ZI  = "Z"; // 字牌（東南西北中發白）

// ── 建立完整牌山 ────────────────────────────────────────────────
// 共 136 張（萬/筒/索×108 + 字牌×28）+ 花牌 16 + 飛 4，隨機洗牌後回傳
function createFullWall() {
  /** @type {string[]} */
  const tiles = [];

  // 萬、筒、索：1-9 各四張
  [SUIT_MAN, SUIT_PIN, SUIT_SOU].forEach((suit) => {
    for (let v = 1; v <= 9; v++) {
      for (let i = 0; i < 4; i++) {
        tiles.push(`${suit}${v}`);
      }
    }
  });

  // 字牌：東南西北白發中（1-7）各四張
  for (let v = 1; v <= 7; v++) {
    for (let i = 0; i < 4; i++) {
      tiles.push(`${SUIT_ZI}${v}`);
    }
  }

  // 花牌：F1-F16 各一張（春夏秋冬梅蘭竹菊 + 琴棋書畫貓雞蟲鼠）
  for (let v = 1; v <= 16; v++) {
    tiles.push(`F${v}`);
  }

  // 飛：H1-H4 各一張
  for (let v = 1; v <= 4; v++) {
    tiles.push(`H${v}`);
  }

  return shuffle(tiles);
}

// ── Fisher-Yates 洗牌（不改動原陣列，回傳新陣列）──────────────
function shuffle(array) {
  const a = array.slice();
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

// ── 手牌排序（僅顯示用，不影響遊戲邏輯）──────────────────────
// 順序：萬(M) → 筒(P) → 索(S) → 字(Z) → 飛(H) → 花(F)
// 同花色內依點數升冪排列
function sortHand(tiles) {
  const orderSuit = { [SUIT_MAN]: 0, [SUIT_PIN]: 1, [SUIT_SOU]: 2, [SUIT_ZI]: 3, H: 4, F: 5 };
  return tiles
    .slice()
    .sort((a, b) => {
      const sa = orderSuit[a[0]];
      const sb = orderSuit[b[0]];
      if (sa !== sb) return sa - sb;
      const va = parseInt(a.slice(1), 10);
      const vb = parseInt(b.slice(1), 10);
      return va - vb;
    });
}

// ── 胡牌判斷（按花色獨立計算「最少需要幾張飛」）─────────────────
// 規則：4副面子（刻子/順子）+ 1對將，飛(H)可替代任意1張
// 原理：各花色互不影響，先算每個花色湊齊面子最少要補幾張飛；
//       選定將牌後，各花色所需飛數之和 ≤ 手上飛數即胡牌
//       （多餘的飛必為 3 的倍數，可自成刻子）。
// 每個花色的 9 格計數壓成一個整數作快取鍵，結果全局複用。
const _suitCache = new Map();

// 單一數牌花色：arr[0..8] 為 1-9 的張數 → 湊齊面子最少需補的飛數
function _suitNeed(arr, key) {
  let hit = _suitCache.get(key);
  if (hit !== undefined) return hit;
  hit = _suitNeedRec(arr);
  _suitCache.set(key, hit);
  return hit;
}
function _suitNeedRec(arr) {
  const ck = _encode(arr);
  const c0 = _suitCache.get(ck);
  if (c0 !== undefined) return c0;
  const r0 = _suitNeedCalc(arr);
  _suitCache.set(ck, r0);
  return r0;
}
function _suitNeedCalc(arr) {
  let i = 0;
  while (i < 9 && arr[i] === 0) i++;
  if (i === 9) return 0;
  let best = 9;
  // 刻子：用 3/2/1 張真牌 + 0/1/2 飛
  for (let real = Math.min(3, arr[i]); real >= 1; real--) {
    arr[i] -= real;
    const r = 3 - real + _suitNeedRec(arr);
    arr[i] += real;
    if (r < best) best = r;
  }
  // 順子：起點取 min(i,6)（8、9 只能落在 789 序列內）
  const base = Math.min(i, 6);
  let used = [], miss = 0;
  for (let j = base; j < base + 3; j++) {
    if (arr[j] > 0) { arr[j]--; used.push(j); } else miss++;
  }
  if (used.length >= 1) {
    const r = miss + _suitNeedRec(arr);
    if (r < best) best = r;
  }
  for (const j of used) arr[j]++;
  return best;
}
function _encode(arr) {
  let k = 0;
  for (let i = 0; i < 9; i++) k = k * 8 + arr[i];
  return k;
}
// 字牌：只能刻子
function _ziNeed(arr) {
  let n = 0;
  for (let i = 0; i < 7; i++) n += (3 - (arr[i] % 3)) % 3;
  return n;
}

function isWinningHand(tiles) {
  if (!tiles || tiles.length % 3 !== 2) return false;

  const suits = { M: new Array(9).fill(0), P: new Array(9).fill(0), S: new Array(9).fill(0), Z: new Array(9).fill(0) };
  let fei = 0;
  for (const t of tiles) {
    const c = t[0];
    if (c === "H") fei++;
    else if (suits[c]) suits[c][parseInt(t.slice(1), 10) - 1]++;
  }
  const names = ["M", "P", "S", "Z"];
  const need = (n, arr) => (n === "Z" ? _ziNeed(arr) : _suitNeed(arr, _encode(arr)));
  const base = {};
  let total = 0;
  for (const n of names) { base[n] = need(n, suits[n]); total += base[n]; }

  // 2 飛作將
  if (fei >= 2 && total <= fei - 2) return true;

  // 真牌作將（對子 / 單張+1飛）
  for (const n of names) {
    const arr = suits[n];
    const limit = n === "Z" ? 7 : 9;
    for (let i = 0; i < limit; i++) {
      if (arr[i] === 0) continue;
      const pairReal = arr[i] >= 2;
      if (!pairReal && fei < 1) continue;
      const cost = pairReal ? 0 : 1;
      arr[i] -= pairReal ? 2 : 1;
      const after = total - base[n] + need(n, arr);
      arr[i] += pairReal ? 2 : 1;
      if (after + cost <= fei) return true;
    }
  }
  return false;
}

// ── 牌陣列 → 計數物件 { "M1": 2, "P3": 1, ... } ──────────────
function toCounts(tiles) {
  const c = {};
  for (const t of tiles) c[t] = (c[t] || 0) + 1;
  return c;
}

// ── 對外保留舊介面（counts 物件版）────────────────────────────
function canFormMeldsWithFei(counts, feiCount) {
  const arrs = { M: new Array(9).fill(0), P: new Array(9).fill(0), S: new Array(9).fill(0), Z: new Array(9).fill(0) };
  for (const k of Object.keys(counts)) if (arrs[k[0]]) arrs[k[0]][parseInt(k.slice(1), 10) - 1] += counts[k];
  let total = 0;
  for (const n of ["M", "P", "S"]) total += _suitNeed(arrs[n], _encode(arrs[n]));
  total += _ziNeed(arrs.Z);
  return total <= feiCount && (feiCount - total) % 3 === 0;
}
function canFormMelds(counts) { return canFormMeldsWithFei(counts, 0); }

// ── 簡單 AI 棄牌策略（供 easy 難度使用）───────────────────────
// 優先順序：
//   1. 優先保留飛萬用牌（最後才棄）
//   2. 優先棄字牌（東南西北中發白）
//   3. 其次棄離其他牌最遠的孤張（鄰近度分數最低）
function chooseAiDiscard(hand) {
  if (!hand || hand.length === 0) return null;

  // 避免改動原手牌
  const tiles = sortHand(hand);

  // 飛優先保留（萬用牌），除非沒其他選擇
  const feiTiles = tiles.filter((t) => t[0] === "H");
  const nonFei = tiles.filter((t) => t[0] !== "H");
  if (nonFei.length === 0 && feiTiles.length > 0) return feiTiles[0];

  // 優先丟字牌，然後優先丟數牌中離其他牌最遠的
  // 只丟「單張」字牌；對子/刻子字牌要保留
  const cnt = toCounts(nonFei);
  const ziSingles = nonFei.filter((t) => t[0] === SUIT_ZI && cnt[t] === 1);
  if (ziSingles.length > 0) return ziSingles[0];

  // 對每張牌算一個「鄰近度」分數，越小越「孤立」（不考慮飛）
  const toScore = nonFei.length ? nonFei : feiTiles;
  let bestTile = toScore[0];
  let bestScore = Infinity;
  for (let t of toScore) {
    const s = t[0];
    const v = parseInt(t.slice(1), 10);
    const neighbors = toScore.filter((other) => {
      if (other === t) return false;
      if (other[0] !== s) return false;
      const ov = parseInt(other.slice(1), 10);
      return Math.abs(ov - v) <= 2;
    });
    const score = neighbors.length + (cnt[t] - 1) * 3; // 對子/刻子加權，避免被拆
    if (score < bestScore) {
      bestScore = score;
      bestTile = t;
    }
  }
  return bestTile;
}

// ── 掛載到全域 window.MJ，供 game.js / game3p.js 呼叫 ─────────
window.MJ = {
  createFullWall,
  sortHand,
  isWinningHand,
  chooseAiDiscard,
  toCounts,
  canFormMelds,
  canFormMeldsWithFei,
};

