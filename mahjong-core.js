// ══════════════════════════════════════════════════════════════
// mahjong-core.js
// 麻將核心工具庫（由 game.js / game3p.js 共用）
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

// ── 胡牌判斷 ────────────────────────────────────────────────
// 規則：4副面子（刻子/順子）+ 1對將，飛牌可替代任意1張
// 枚舉所有可能的將牌後呼叫 canFormMeldsWithFei() 遞迴驗證
// 不判斷七對/十三么等特殊牌型（由 classifyWinningHand 處理）
function isWinningHand(tiles) {
  if (!tiles || tiles.length % 3 !== 2) return false;

  const raw = tiles.filter((t) => t[0] !== "H");
  const feiCount = tiles.length - raw.length;
  const counts = toCounts(raw);

  // 試每一種可能作將的牌（含用飛當將）
  for (let key of Object.keys(counts)) {
    if (counts[key] >= 2) {
      counts[key] -= 2;
      if (canFormMeldsWithFei(counts, feiCount)) {
        counts[key] += 2;
        return true;
      }
      counts[key] += 2;
    } else if (counts[key] >= 1 && feiCount >= 1) {
      counts[key] -= 1;
      if (canFormMeldsWithFei(counts, feiCount - 1)) {
        counts[key] += 1;
        return true;
      }
      counts[key] += 1;
    } else if (feiCount >= 2) {
      if (canFormMeldsWithFei(counts, feiCount - 2)) return true;
    }
  }
  if (feiCount >= 2 && canFormMeldsWithFei(counts, feiCount - 2)) return true;
  return false;
}

// ── 牌陣列 → 計數物件 { "M1": 2, "P3": 1, ... } ──────────────
function toCounts(tiles) {
  /** @type {Record<string, number>} */
  const c = {};
  for (let t of tiles) {
    c[t] = (c[t] || 0) + 1;
  }
  return c;
}

// ── 遞迴面子分解（支援飛萬用）─────────────────────────────────
// 策略：取第一個非零牌，嘗試組成：
//   1. 刻子（0/1/2 張飛）
//   2. 順子（firstKey 可作為 pos=0/1/2，即序列首/中/尾）
// 修正說明：支援 firstKey 在序列任意位，解決 [8,9,飛]→789 被漏判的問題
function canFormMeldsWithFei(counts, feiCount) {
  // 找第一個非零鍵
  let firstKey = null;
  for (const key of Object.keys(counts)) {
    if (counts[key] > 0) { firstKey = key; break; }
  }
  if (!firstKey) return feiCount % 3 === 0;

  const suit = firstKey[0];
  const v    = parseInt(firstKey.slice(1), 10);

  // ── 1. 刻子（0/1/2 張飛代替）────────────────────────
  for (let f = 0; f <= Math.min(2, feiCount); f++) {
    const real = 3 - f;
    if (counts[firstKey] >= real) {
      counts[firstKey] -= real;
      if (canFormMeldsWithFei(counts, feiCount - f)) {
        counts[firstKey] += real;
        return true;
      }
      counts[firstKey] += real;
    }
  }

  // ── 2. 順子（數牌；firstKey 可在序列第 0/1/2 位）───────
  // pos=0: [firstKey, v+1, v+2]  ← 原本只有這個
  // pos=1: [v-1, firstKey, v+1]  ← 新增，例 8 在中間 → 7+8+9
  // pos=2: [v-2, v-1, firstKey]  ← 新增，例 9 在末位 → 7+8+9
  if (suit !== SUIT_ZI) {
    for (let pos = 0; pos <= 2; pos++) {
      const base = v - pos;
      if (base < 1 || base + 2 > 9) continue; // 序列超出 1-9

      const k = [
        `${suit}${base}`,
        `${suit}${base + 1}`,
        `${suit}${base + 2}`,
      ];

      // 計算每個非 firstKey 位置需要幾張飛，並記錄是否用真實牌
      let feisNeeded = 0;
      const useReal = [false, false, false]; // true = 用手牌真實牌
      for (let i = 0; i < 3; i++) {
        if (i === pos) { useReal[i] = true; continue; } // firstKey 自身
        if ((counts[k[i]] || 0) > 0) {
          useReal[i] = true; // 有真實牌
        } else {
          feisNeeded++;      // 需要用飛代替
        }
      }
      if (feisNeeded > feiCount) continue;

      // 消耗
      counts[firstKey]--;
      for (let i = 0; i < 3; i++) {
        if (i !== pos && useReal[i]) counts[k[i]]--;
      }

      const ok = canFormMeldsWithFei(counts, feiCount - feisNeeded);

      // 恢復
      counts[firstKey]++;
      for (let i = 0; i < 3; i++) {
        if (i !== pos && useReal[i]) counts[k[i]]++;
      }

      if (ok) return true;
    }
  }

  return false;
}

// ── 無飛版面子分解（純手牌檢查，不使用飛萬用）────────────────
function canFormMelds(counts) {
  return canFormMeldsWithFei(counts, 0);
}

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
  const ziTiles = nonFei.filter((t) => t[0] === SUIT_ZI);
  if (ziTiles.length > 0) {
    return ziTiles[0];
  }

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
    const score = neighbors.length;
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
};

