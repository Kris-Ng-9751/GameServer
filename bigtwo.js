'use strict';
// ═══════════════════════════════════════════════════════════════
// 锄大地 Big Two — 游戏逻辑
// 四人、52张牌、先出完者胜。牌力 3 最小，2 最大；花色 ♦<♣<♥<♠
// ═══════════════════════════════════════════════════════════════

const SUITS = ['♦', '♣', '♥', '♠'];
const SUIT_ORDER = { '♦': 0, '♣': 1, '♥': 2, '♠': 3 };
const CARD_VALS = ['3', '4', '5', '6', '7', '8', '9', '10', 'J', 'Q', 'K', 'A', '2'];
const RANK_VAL = { '3': 0, '4': 1, '5': 2, '6': 3, '7': 4, '8': 5, '9': 6, '10': 7, 'J': 8, 'Q': 9, 'K': 10, 'A': 11, '2': 12 };

const TYPE_LABEL = {
  single: '单张',
  pair: '对子',
  triple: '三张',
  straight: '顺子',
  flush: '同花',
  full_house: '葫芦',
  four_of_a_kind: '四条',
  straight_flush: '同花顺'
};

const G = {
  phase: 'idle',
  players: [
    { id: 0, name: '玩家', type: 'human', cards: [] },
    { id: 1, name: '人机1', type: 'ai', cards: [] },
    { id: 2, name: '人机2', type: 'ai', cards: [] },
    { id: 3, name: '人机3', type: 'ai', cards: [] }
  ],
  currentPlayerIdx: 0,
  lastPlayInfo: null,
  lastActivePlay: null,
  selectedCards: [],
  passCount: 0,
  firstPlayerThisRound: null
};

function createDeck() {
  const deck = [];
  for (const suit of SUITS) {
    for (const val of CARD_VALS) {
      deck.push({
        suit,
        value: val,
        rankVal: RANK_VAL[val],
        suitOrder: SUIT_ORDER[suit],
        isRed: suit === '♥' || suit === '♦',
        id: `${suit}${val}`
      });
    }
  }
  return deck;
}

function shuffle(arr) {
  const a = [...arr];
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

// 锄大地排序：先按点数 3..2，再按花色 ♦♣♥♠
function sortCards(cards) {
  return [...cards].sort((a, b) => {
    if (a.rankVal !== b.rankVal) return a.rankVal - b.rankVal;
    return a.suitOrder - b.suitOrder;
  });
}

// 找持有 3♦ 的玩家
function findFirstPlayer() {
  for (let i = 0; i < 4; i++) {
    const has = G.players[i].cards.some(c => c.id === '♦3');
    if (has) return i;
  }
  return 0;
}

function getFreq(cards) {
  const f = {};
  cards.forEach(c => { f[c.rankVal] = (f[c.rankVal] || 0) + 1; });
  return f;
}

// 比较两张单牌：a 是否大于 b
function cardGreater(a, b) {
  if (a.rankVal !== b.rankVal) return a.rankVal > b.rankVal;
  return a.suitOrder > b.suitOrder;
}

// 取一组牌中“最大”的一张（按锄大地规则）
function maxCard(cards) {
  return cards.reduce((m, c) => cardGreater(c, m) ? c : m);
}

function analyzeHand(cards) {
  if (!cards || cards.length === 0) return null;
  const n = cards.length;
  const freq = getFreq(cards);
  const ranks = Object.keys(freq).map(Number).sort((a, b) => a - b);
  const counts = ranks.map(r => freq[r]);

  if (n === 1) return { type: 'single', rank: cards[0].rankVal, suitOrder: cards[0].suitOrder, n, high: cards[0] };
  if (n === 2) {
    if (ranks.length === 1) {
      const high = maxCard(cards);
      return { type: 'pair', rank: ranks[0], suitOrder: high.suitOrder, n, high };
    }
    return null;
  }
  if (n === 3) {
    if (ranks.length === 1) return { type: 'triple', rank: ranks[0], n };
    return null;
  }
  if (n === 5) {
    const sorted = sortCards(cards);
    const isFlush = sorted.every(c => c.suit === sorted[0].suit);
    const rankSet = [...new Set(sorted.map(c => c.rankVal))].sort((a, b) => a - b);

    // 顺子：连续 5 张，2 不参与（3-4-5-6-7 到 10-J-Q-K-A）
    const isStraight = rankSet.length === 5 && rankSet.every((r, i) => i === 0 || r === rankSet[i - 1] + 1) && rankSet[4] !== 12;
    if (isStraight && isFlush) return { type: 'straight_flush', rank: rankSet[4], suitOrder: sorted[4].suitOrder, n, high: sorted[4] };
    if (isStraight) return { type: 'straight', rank: rankSet[4], suitOrder: sorted[4].suitOrder, n, high: sorted[4] };
    if (isFlush) return { type: 'flush', rank: sorted[4].rankVal, suitOrder: sorted[4].suitOrder, n, high: sorted[4] };

    // 四条
    if (counts.some(c => c === 4)) {
      const quadRank = ranks[counts.indexOf(4)];
      return { type: 'four_of_a_kind', rank: quadRank, n };
    }
    // 葫芦
    if (counts.some(c => c === 3) && counts.some(c => c === 2)) {
      const triRank = ranks[counts.indexOf(3)];
      return { type: 'full_house', rank: triRank, n };
    }
  }
  if (n === 4 && counts.length === 1 && counts[0] === 4) return { type: 'four_of_a_kind', rank: ranks[0], n };
  return { type: 'invalid', n };
}

// 是否可压过上家
function canBeat(newCards, lastPlay) {
  const h = analyzeHand(newCards);
  if (!h || h.type === 'invalid') return false;
  if (!lastPlay) return true;

  const bombOrder = ['straight_flush', 'four_of_a_kind'];
  const lastBomb = bombOrder.indexOf(lastPlay.type);
  const newBomb = bombOrder.indexOf(h.type);

  if (newBomb >= 0 && lastBomb < 0) return true;
  if (newBomb < 0 && lastBomb >= 0) return false;
  if (newBomb >= 0 && lastBomb >= 0) {
    if (newBomb !== lastBomb) return newBomb > lastBomb;
    if (h.type === 'straight_flush') return h.rank > lastPlay.rank || (h.rank === lastPlay.rank && h.suitOrder > lastPlay.suitOrder);
    return h.rank > lastPlay.rank;
  }

  if (h.type !== lastPlay.type) return false;
  if (h.n !== lastPlay.n) return false;

  if (h.type === 'single' || h.type === 'pair') {
    if (h.rank !== lastPlay.rank) return h.rank > lastPlay.rank;
    return (h.suitOrder != null && lastPlay.suitOrder != null) && h.suitOrder > lastPlay.suitOrder;
  }
  if (h.type === 'straight' || h.type === 'flush') {
    if (h.rank !== lastPlay.rank) return h.rank > lastPlay.rank;
    return (h.suitOrder != null && lastPlay.suitOrder != null) && h.suitOrder > lastPlay.suitOrder;
  }
  return h.rank > lastPlay.rank;
}

function initGame() {
  const deck = shuffle(createDeck());
  G.phase = 'playing';
  for (let i = 0; i < 4; i++) {
    G.players[i].cards = sortCards(deck.slice(i * 13, (i + 1) * 13));
  }
  G.currentPlayerIdx = findFirstPlayer();
  G.firstPlayerThisRound = G.currentPlayerIdx;
  G.lastPlayInfo = null;
  G.lastActivePlay = null;
  G.selectedCards = [];
  G.passCount = 0;
  render();
  if (typeof showMsg === 'function') showMsg('持 3♦ 者先出', 1200);
  if (G.players[G.currentPlayerIdx].type === 'ai') setTimeout(aiPlay, 1000);
}

function humanPlay(selectedCards) {
  if (G.phase !== 'playing') return;
  if (G.currentPlayerIdx !== 0) return;
  if (!selectedCards || selectedCards.length === 0) return;

  const handType = analyzeHand(selectedCards);
  if (!handType || handType.type === 'invalid') {
    if (typeof showMsg === 'function') showMsg('无效牌型', 800);
    return;
  }
  const lastPlay = G.lastActivePlay;
  if (lastPlay && lastPlay.playerIdx !== 0) {
    if (!canBeat(selectedCards, lastPlay.handType)) {
      if (typeof showMsg === 'function') showMsg('无法压过上家', 800);
      return;
    }
  }
  doPlay(0, selectedCards, handType);
}

function humanPass() {
  if (G.phase !== 'playing') return;
  if (G.currentPlayerIdx !== 0) return;
  if (!G.lastActivePlay || G.lastActivePlay.playerIdx === 0) {
    if (typeof showMsg === 'function') showMsg('轮到你出牌，不能过', 800);
    return;
  }
  doPass(0);
}

function doPlay(playerIdx, cards, handType) {
  const p = G.players[playerIdx];
  const ids = cards.map(c => c.id);
  p.cards = p.cards.filter(c => !ids.includes(c.id));
  const playInfo = { playerIdx, cards: [...cards], handType };
  G.lastPlayInfo = playInfo;
  G.lastActivePlay = playInfo;
  G.passCount = 0;
  G.selectedCards = [];

  if (p.cards.length === 0) {
    G.phase = 'gameover';
    render();
    if (typeof onBigTwoGameOver === 'function') onBigTwoGameOver(playerIdx);
    return;
  }
  nextPlayer();
  render();
  if (G.players[G.currentPlayerIdx].type === 'ai') setTimeout(aiPlay, 800);
}

function doPass(playerIdx) {
  G.lastPlayInfo = { playerIdx, cards: [], handType: null, isPassed: true };
  G.passCount++;
  if (G.passCount >= 3) {
    G.lastActivePlay = null;
    G.passCount = 0;
    G.firstPlayerThisRound = G.currentPlayerIdx;
  }
  nextPlayer();
  render();
  if (G.players[G.currentPlayerIdx].type === 'ai') setTimeout(aiPlay, 800);
}

function nextPlayer() {
  G.currentPlayerIdx = (G.currentPlayerIdx + 1) % 4;
}

function aiPlay() {
  if (G.phase !== 'playing') return;
  const playerIdx = G.currentPlayerIdx;
  if (G.players[playerIdx].type !== 'ai') return;

  const cards = G.players[playerIdx].cards;
  const lastPlay = G.lastActivePlay;

  if (!lastPlay || lastPlay.playerIdx === playerIdx) {
    const play = aiChooseLead(playerIdx, cards);
    const ht = analyzeHand(play);
    if (ht && ht.type !== 'invalid') doPlay(playerIdx, play, ht);
  } else {
    const play = aiChooseFollow(playerIdx, cards, lastPlay.handType);
    if (play) {
      const ht = analyzeHand(play);
      doPlay(playerIdx, play, ht);
    } else {
      doPass(playerIdx);
    }
  }
}

function aiChooseLead(playerIdx, cards) {
  const sorted = sortCards(cards);
  const freq = getFreq(cards);

  if (cards.length <= 2) return cards;

  const straight = findStraight(cards);
  if (straight && cards.length >= 8) return straight;

  for (const c of sorted) {
    if (freq[c.rankVal] >= 3) return cards.filter(x => x.rankVal === c.rankVal).slice(0, 3);
  }
  for (const c of sorted) {
    if (freq[c.rankVal] >= 2) return cards.filter(x => x.rankVal === c.rankVal).slice(0, 2);
  }
  return [sorted[0]];
}

function findStraight(cards) {
  const rankSet = [...new Set(cards.map(c => c.rankVal))].filter(r => r !== 12).sort((a, b) => a - b);
  for (let i = 0; i <= rankSet.length - 5; i++) {
    const seq = rankSet.slice(i, i + 5);
    if (seq.every((r, j) => j === 0 || r === seq[j - 1] + 1)) {
      const hand = seq.map(r => cards.find(c => c.rankVal === r));
      if (hand.every(Boolean)) return hand;
    }
  }
  return null;
}

function aiChooseFollow(playerIdx, cards, lastHT) {
  if (!lastHT) return null;
  const sorted = sortCards(cards);

  if (lastHT.type === 'single') {
    const better = sorted.filter(c => cardGreater(c, lastHT.high));
    if (better.length) return [better[0]];
  }
  if (lastHT.type === 'pair') {
    const pairs = [];
    const freq = getFreq(cards);
    for (const r of Object.keys(freq).map(Number)) {
      if (freq[r] >= 2 && r > lastHT.rank) {
        const pair = cards.filter(c => c.rankVal === r).slice(0, 2);
        pairs.push(pair);
      }
    }
    if (pairs.length) return pairs[0];
  }
  if (lastHT.type === 'triple') {
    const freq = getFreq(cards);
    for (const r of Object.keys(freq).map(Number)) {
      if (freq[r] >= 3 && r > lastHT.rank) return cards.filter(c => c.rankVal === r).slice(0, 3);
    }
  }
  if (lastHT.type === 'straight' || lastHT.type === 'flush' || lastHT.type === 'straight_flush') {
    const fives = findAllFiveCardHands(cards, lastHT.type);
    const better = fives.filter(h => canBeat(h, lastHT));
    if (better.length) return better[0];
  }
  if (lastHT.type === 'full_house') {
    const freq = getFreq(cards);
    const triVals = Object.keys(freq).map(Number).filter(r => freq[r] >= 3 && r > lastHT.rank);
    for (const r of triVals) {
      const tri = cards.filter(c => c.rankVal === r).slice(0, 3);
      const pairEntry = Object.entries(freq).find(([vr, cnt]) => +vr !== r && cnt >= 2);
      if (pairEntry) {
        const pair = cards.filter(c => c.rankVal === +pairEntry[0]).slice(0, 2);
        return [...tri, ...pair];
      }
    }
  }
  if (lastHT.type === 'four_of_a_kind') {
    const freq = getFreq(cards);
    for (const r of Object.keys(freq).map(Number)) {
      if (freq[r] >= 4 && r > lastHT.rank) return cards.filter(c => c.rankVal === r);
    }
  }
  return null;
}

function findAllFiveCardHands(cards, type) {
  const out = [];
  const n = cards.length;
  if (n < 5) return out;
  const indices = [];
  function collect(start, depth) {
    if (depth === 5) {
      const hand = indices.map(i => cards[i]);
      const ht = analyzeHand(hand);
      if (ht && ht.type === type) out.push(hand);
      return;
    }
    for (let i = start; i < n; i++) {
      indices[depth] = i;
      collect(i + 1, depth + 1);
    }
  }
  collect(0, 0);
  return out;
}

function createCardEl(card, selectable) {
  const el = document.createElement('div');
  el.className = 'card' + (card.isRed ? ' card-red' : '') +
    (selectable && G.selectedCards.some(c => c.id === card.id) ? ' selected' : '');
  el.dataset.id = card.id;
  el.innerHTML = `
    <div class="card-top">
      <span class="card-val">${card.value}</span>
      <span class="card-suit">${card.suit}</span>
    </div>
    <div class="card-mid">${card.suit}</div>
    <div class="card-bot">
      <span class="card-val">${card.value}</span>
      <span class="card-suit">${card.suit}</span>
    </div>`;
  return el;
}

function createCardBack() {
  const el = document.createElement('div');
  el.className = 'card card-back';
  el.innerHTML = '<div class="card-back-pattern">🂠</div>';
  return el;
}

function toggleSelectCard(card) {
  if (G.phase !== 'playing' || G.currentPlayerIdx !== 0) return;
  const idx = G.selectedCards.findIndex(c => c.id === card.id);
  if (idx >= 0) G.selectedCards.splice(idx, 1);
  else G.selectedCards.push(card);
  renderPlayerArea(0);
  updatePlayBtn();
}

function render() {
  renderPlayers();
  renderCenter();
  renderActionBar();
  renderTurnIndicator();
}

function renderPlayers() {
  G.players.forEach((p, i) => renderPlayerArea(i));
}

function renderPlayerArea(idx) {
  const p = G.players[idx];
  const area = document.getElementById(`player-area-${idx}`);
  if (!area) return;

  const nameEl = area.querySelector('.player-name');
  if (nameEl) {
    nameEl.textContent = p.name;
    nameEl.classList.toggle('is-current', G.currentPlayerIdx === idx && G.phase === 'playing');
  }

  const handEl = area.querySelector('.hand-cards');
  if (!handEl) return;
  handEl.innerHTML = '';

  const countEl = area.querySelector('.card-count');
  if (countEl) countEl.textContent = p.cards.length + '张';

  if (idx === 0) {
    p.cards.forEach(card => {
      const el = createCardEl(card, true);
      el.addEventListener('click', () => toggleSelectCard(card));
      handEl.appendChild(el);
    });
  } else {
    const count = p.cards.length;
    for (let i = 0; i < Math.min(count, 18); i++) {
      handEl.appendChild(createCardBack());
    }
  }
}

function renderCenter() {
  const lastEl = document.getElementById('last-play-center');
  if (!lastEl) return;
  lastEl.innerHTML = '';
  const lp = G.lastActivePlay;
  if (lp && !lp.isPassed) {
    lp.cards.forEach(c => {
      const ce = createCardEl(c, false);
      ce.style.transform = 'scale(0.8)';
      lastEl.appendChild(ce);
    });
    const typeLabel = document.createElement('div');
    typeLabel.className = 'play-type-label';
    typeLabel.textContent = (lp.handType && TYPE_LABEL[lp.handType.type]) || '';
    lastEl.appendChild(typeLabel);
  } else if (lp && lp.isPassed && G.lastPlayInfo && G.lastPlayInfo.playerIdx === lp.playerIdx) {
    lastEl.innerHTML = '<div class="pass-label">不出</div>';
  }
}

function renderActionBar() {
  const bar = document.getElementById('action-bar');
  if (!bar) return;
  const isMyTurn = G.phase === 'playing' && G.currentPlayerIdx === 0;
  bar.style.display = isMyTurn ? 'flex' : 'none';
  const canPass = G.lastActivePlay && G.lastActivePlay.playerIdx !== 0;
  const passBtn = document.getElementById('btn-pass');
  if (passBtn) passBtn.disabled = !canPass;
  updatePlayBtn();
}

function updatePlayBtn() {
  const playBtn = document.getElementById('btn-play');
  if (!playBtn) return;
  const isMyTurn = G.phase === 'playing' && G.currentPlayerIdx === 0;
  const hasSelected = G.selectedCards.length > 0;
  const lastPlay = G.lastActivePlay;
  let canPlay = isMyTurn && hasSelected;
  if (canPlay && lastPlay && lastPlay.playerIdx !== 0) {
    canPlay = canBeat(G.selectedCards, lastPlay.handType);
  } else if (canPlay) {
    const ht = analyzeHand(G.selectedCards);
    canPlay = ht && ht.type !== 'invalid';
  }
  playBtn.disabled = !canPlay;
  playBtn.className = 'btn-action btn-play' + (canPlay ? ' btn-active' : '');
}

function renderTurnIndicator() {
  [0, 1, 2, 3].forEach(i => {
    const area = document.getElementById(`player-area-${i}`);
    if (!area) return;
    const ind = area.querySelector('.turn-indicator');
    if (ind) ind.style.display = (G.phase === 'playing' && G.currentPlayerIdx === i) ? 'inline-block' : 'none';
  });
}
