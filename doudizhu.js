'use strict';
// ============================================================
// 斗地主 — 完整游戏逻辑
// ============================================================

// ---------- 常量 ----------
const SUITS      = ['♠','♥','♦','♣'];
const CARD_VALS  = ['3','4','5','6','7','8','9','10','J','Q','K','A','2'];
const NUM_VAL    = {
  '3':3,'4':4,'5':5,'6':6,'7':7,'8':8,'9':9,'10':10,
  'J':11,'Q':12,'K':13,'A':14,'2':15,'小王':16,'大王':17
};
const TYPE_LABEL = {
  single:'单张', pair:'对子', triple:'三张',
  triple_single:'三带一', triple_pair:'三带二',
  straight:'顺子', double_straight:'连对',
  triple_straight:'飞机', plane_single:'飞机带单',
  plane_pair:'飞机带对', bomb:'炸弹', rocket:'王炸'
};

// ---------- 游戏状态 ----------
const G = {
  phase: 'idle',           // idle | bidding | playing | gameover
  players: [
    { id:0, name:'玩家', type:'human', cards:[], isLandlord:false, score:0 },
    { id:1, name:'人机1', type:'ai',   cards:[], isLandlord:false, score:0 },
    { id:2, name:'人机2', type:'ai',   cards:[], isLandlord:false, score:0 }
  ],
  bottomCards: [],
  landlordIdx: -1,
  currentPlayerIdx: 0,
  lastPlayInfo: null,       // { playerIdx, cards, handType }
  lastActivePlay: null,     // last non-pass play info (for display)
  selectedCards: [],
  bidOrder: [],
  bidIdx: 0,
  passCount: 0,
  baseScore: 1,
  bombCount: 0,
  roundScores: [0,0,0],
  betPerPoint: 10,          // coins per scoring point
  lastRoundDelta0: 0        // player 0's score change this round (for balance settlement)
};

// ---------- 牌组 ----------
function createDeck() {
  const deck = [];
  for (const suit of SUITS) {
    for (const val of CARD_VALS) {
      deck.push({ suit, value:val, numVal:NUM_VAL[val],
        isRed: suit==='♥'||suit==='♦', id:`${suit}${val}` });
    }
  }
  deck.push({ suit:'joker', value:'小王', numVal:16, isRed:false, id:'joker_s' });
  deck.push({ suit:'joker', value:'大王', numVal:17, isRed:true,  id:'joker_b' });
  return deck;
}

function shuffle(arr) {
  const a = [...arr];
  for (let i = a.length-1; i>0; i--) {
    const j = Math.floor(Math.random()*(i+1));
    [a[i],a[j]] = [a[j],a[i]];
  }
  return a;
}

function sortCards(cards) {
  return [...cards].sort((a,b) =>
    a.numVal !== b.numVal ? a.numVal-b.numVal : SUITS.indexOf(a.suit)-SUITS.indexOf(b.suit)
  );
}

// ---------- 牌型分析 ----------
function getFreq(cards) {
  const f = {};
  cards.forEach(c => f[c.numVal] = (f[c.numVal]||0)+1);
  return f;
}

function analyzeHand(cards) {
  if (!cards || cards.length===0) return null;
  const n = cards.length;
  const freq = getFreq(cards);
  const vals = Object.keys(freq).map(Number).sort((a,b)=>a-b);
  const counts = vals.map(v => freq[v]);

  // 王炸
  if (n===2 && freq[16] && freq[17]) return { type:'rocket', rank:17, n };
  // 炸弹
  if (n===4 && counts.length===1 && counts[0]===4) return { type:'bomb', rank:vals[0], n };
  // 单张
  if (n===1) return { type:'single', rank:vals[0], n };
  // 对子
  if (n===2 && counts[0]===2) return { type:'pair', rank:vals[0], n };
  // 三张
  if (n===3 && counts[0]===3) return { type:'triple', rank:vals[0], n };
  // 三带一
  if (n===4 && counts.includes(3) && counts.includes(1)) {
    const rank = vals[counts.indexOf(3)];
    return { type:'triple_single', rank, n };
  }
  // 三带二
  if (n===5 && counts.includes(3) && counts.includes(2)) {
    const rank = vals[counts.indexOf(3)];
    return { type:'triple_pair', rank, n };
  }
  // 顺子 / 连对 / 飞机（纯）
  if (vals.every(v => v<=14)) {
    const isConsec = vals.every((v,i) => i===0 || v===vals[i-1]+1);
    if (isConsec) {
      if (counts.every(c=>c===1) && n>=5)
        return { type:'straight', rank:vals[n-1], n };
      if (counts.every(c=>c===2) && vals.length>=3)
        return { type:'double_straight', rank:vals[vals.length-1], n };
      if (counts.every(c=>c===3) && vals.length>=2)
        return { type:'triple_straight', rank:vals[vals.length-1], n };
    }
  }
  // 飞机带翅膀
  const plane = detectPlane(freq, n);
  if (plane) return plane;

  return { type:'invalid', n };
}

function detectPlane(freq, n) {
  const triVals = Object.keys(freq).map(Number)
    .filter(v => v<=14 && freq[v]>=3).sort((a,b)=>a-b);
  if (triVals.length < 2) return null;

  for (let s=0; s<triVals.length; s++) {
    let len = 1;
    while (s+len < triVals.length && triVals[s+len]===triVals[s+len-1]+1) len++;
    for (let k=2; k<=len; k++) {
      const pv = triVals.slice(s, s+k);
      const rem = {...freq};
      pv.forEach(v => rem[v] -= 3);
      if (Object.values(rem).some(c=>c<0)) continue;
      const remSum = Object.values(rem).reduce((a,b)=>a+b, 0);
      if (remSum === k) return { type:'plane_single', rank:pv[k-1], n, k };
      if (remSum === k*2) {
        const re = Object.entries(rem).filter(([,c])=>c>0);
        if (re.every(([,c])=>c%2===0) && re.reduce((a,[,c])=>a+c/2,0)===k)
          return { type:'plane_pair', rank:pv[k-1], n, k };
      }
    }
  }
  return null;
}

function canBeat(newCards, lastPlay) {
  const h = analyzeHand(newCards);
  if (!h || h.type==='invalid') return false;
  if (!lastPlay) return true;
  if (h.type==='rocket') return true;
  if (h.type==='bomb') {
    if (lastPlay.type==='rocket') return false;
    if (lastPlay.type==='bomb') return h.rank > lastPlay.rank;
    return true;
  }
  if (lastPlay.type==='bomb' || lastPlay.type==='rocket') return false;
  if (h.type !== lastPlay.type) return false;
  if (h.n !== lastPlay.n) return false;
  return h.rank > lastPlay.rank;
}

// ---------- 游戏初始化 ----------
function initGame() {
  const deck = shuffle(createDeck());
  G.phase = 'bidding';
  G.bottomCards = deck.slice(0, 3);
  G.players.forEach((p, i) => {
    p.cards = sortCards(deck.slice(3 + i*17, 3 + (i+1)*17));
    p.isLandlord = false;
  });
  G.landlordIdx = -1;
  G.selectedCards = [];
  G.lastPlayInfo = null;
  G.lastActivePlay = null;
  G.passCount = 0;
  G.bombCount = 0;
  G.baseScore = 1;
  // 随机决定叫地主顺序
  G.bidOrder = [0,1,2];
  const startIdx = Math.floor(Math.random()*3);
  G.bidOrder = [...G.bidOrder.slice(startIdx), ...G.bidOrder.slice(0, startIdx)];
  G.bidIdx = 0;
  G.currentPlayerIdx = G.bidOrder[0];
  render();
  // 若AI先叫
  if (G.players[G.currentPlayerIdx].type === 'ai') {
    setTimeout(aiBid, 900);
  }
}

// ---------- 叫地主 ----------
function bid(playerIdx, callIt) {
  if (G.phase !== 'bidding') return;
  if (playerIdx !== G.currentPlayerIdx) return;

  if (callIt) {
    setLandlord(playerIdx);
    return;
  }
  // 不叫 → 下一个
  G.bidIdx++;
  if (G.bidIdx >= 3) {
    // 全部不叫，重新发牌
    showMsg('所有人都不叫，重新发牌！', 1500);
    setTimeout(initGame, 1600);
    return;
  }
  G.currentPlayerIdx = G.bidOrder[G.bidIdx];
  render();
  if (G.players[G.currentPlayerIdx].type === 'ai') {
    setTimeout(aiBid, 900);
  }
}

function setLandlord(playerIdx) {
  G.landlordIdx = playerIdx;
  G.players[playerIdx].isLandlord = true;
  // 地主拿底牌
  G.players[playerIdx].cards = sortCards([
    ...G.players[playerIdx].cards, ...G.bottomCards
  ]);
  G.phase = 'playing';
  G.currentPlayerIdx = playerIdx;
  G.lastPlayInfo = null;
  G.lastActivePlay = null;
  G.passCount = 0;
  render();
  showMsg(`${G.players[playerIdx].name} 成为地主！`, 1200);
  if (G.players[playerIdx].type === 'ai') {
    setTimeout(aiPlay, 1400);
  }
}

function aiBid() {
  const p = G.players[G.currentPlayerIdx];
  const score = evalHandScore(p.cards);
  // 手牌分 > 4 就叫，随机因素 ±1
  const threshold = 4 + (Math.random() < 0.3 ? -1 : 0);
  bid(G.currentPlayerIdx, score >= threshold);
}

function evalHandScore(cards) {
  let s = 0;
  const freq = getFreq(cards);
  cards.forEach(c => {
    if (c.numVal === 17) s += 4;   // 大王
    else if (c.numVal === 16) s += 3; // 小王
    else if (c.numVal === 15) s += 2; // 2
    else if (c.numVal === 14) s += 1; // A
  });
  // 炸弹
  Object.values(freq).forEach(cnt => { if (cnt===4) s += 6; });
  return s;
}

// ---------- 出牌 ----------
function humanPlay(selectedCards) {
  if (G.phase !== 'playing') return;
  if (G.currentPlayerIdx !== 0) return;
  if (!selectedCards || selectedCards.length === 0) return;

  const handType = analyzeHand(selectedCards);
  if (!handType || handType.type === 'invalid') {
    showMsg('无效的牌型！', 800); return;
  }
  const lastPlay = G.lastActivePlay;
  if (lastPlay && lastPlay.playerIdx !== 0) {
    if (!canBeat(selectedCards, lastPlay.handType)) {
      showMsg('无法压过上家出牌！', 800); return;
    }
  }
  doPlay(0, selectedCards, handType);
}

function humanPass() {
  if (G.phase !== 'playing') return;
  if (G.currentPlayerIdx !== 0) return;
  if (!G.lastActivePlay || G.lastActivePlay.playerIdx === 0) {
    showMsg('轮到你出牌，不能过！', 800); return;
  }
  doPass(0);
}

function doPlay(playerIdx, cards, handType) {
  const p = G.players[playerIdx];
  // 从手牌移除
  const ids = cards.map(c=>c.id);
  p.cards = p.cards.filter(c => !ids.includes(c.id));
  // 炸弹/王炸 倍率
  if (handType.type==='bomb' || handType.type==='rocket') {
    G.bombCount++;
  }
  const playInfo = { playerIdx, cards:[...cards], handType };
  G.lastPlayInfo = playInfo;
  G.lastActivePlay = playInfo;
  G.passCount = 0;
  G.selectedCards = [];

  // 检查胜利
  if (p.cards.length === 0) {
    G.phase = 'gameover';
    calcScores(playerIdx);
    render();
    return;
  }
  nextPlayer();
  render();
  if (G.players[G.currentPlayerIdx].type === 'ai') {
    setTimeout(aiPlay, 900);
  }
}

function doPass(playerIdx) {
  G.lastPlayInfo = { playerIdx, cards:[], handType:null, isPassed:true };
  G.passCount++;
  // 如果其他两个都过，当前最后出牌者可自由出牌
  if (G.passCount >= 2) {
    G.lastActivePlay = null;
    G.passCount = 0;
  }
  nextPlayer();
  render();
  if (G.players[G.currentPlayerIdx].type === 'ai') {
    setTimeout(aiPlay, 900);
  }
}

function nextPlayer() {
  G.currentPlayerIdx = (G.currentPlayerIdx + 1) % 3;
}

// ---------- AI 出牌 ----------
function aiPlay() {
  if (G.phase !== 'playing') return;
  const playerIdx = G.currentPlayerIdx;
  if (G.players[playerIdx].type !== 'ai') return;

  const cards = G.players[playerIdx].cards;
  const lastPlay = G.lastActivePlay;

  if (!lastPlay || lastPlay.playerIdx === playerIdx) {
    // 自由出牌
    const play = aiChooseLead(playerIdx, cards);
    const ht = analyzeHand(play);
    doPlay(playerIdx, play, ht);
  } else {
    // 跟牌
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
  // 优先出小单张；若接近赢（≤3张），出所有
  if (cards.length <= 4) return cards;
  const sorted = sortCards(cards);
  const freq = getFreq(cards);

  // 尝试顺子
  const straight = findBestStraight(cards);
  if (straight && cards.length >= 12) return straight;

  // 尝试连对
  const doubleStraight = findBestDoubleStraight(cards);
  if (doubleStraight && doubleStraight.length >= 6) return doubleStraight;

  // 尝试三带x
  const triple = findTriplePlay(cards, null);
  if (triple) return triple;

  // 对子
  for (const c of sorted) {
    if (freq[c.numVal] >= 2) {
      return cards.filter(x => x.numVal===c.numVal).slice(0,2);
    }
  }
  // 单张
  return [sorted[0]];
}

function aiChooseFollow(playerIdx, cards, lastHT) {
  if (!lastHT) return null;
  // 炸弹/王炸处理
  const sorted = sortCards(cards);

  // 尝试以同类型更大的牌压过
  const candidates = findCandidates(cards, lastHT);
  if (candidates.length > 0) {
    // 选最小的
    return candidates[0];
  }

  // 农民策略：如果队友是上家（最后出牌），考虑不出炸弹
  const isPartner = !G.players[lastHT ? G.lastActivePlay?.playerIdx??-1 : -1]?.isLandlord;
  const isTeammate = G.lastActivePlay && 
    G.players[G.lastActivePlay.playerIdx]?.isLandlord === G.players[playerIdx]?.isLandlord;
  
  if (isTeammate && !G.players[playerIdx].isLandlord) {
    // 队友出的，不用压
    return null;
  }

  // 用炸弹
  const bomb = findBomb(cards);
  if (bomb) return bomb;

  // 王炸
  const rocket = cards.filter(c=>c.numVal>=16);
  if (rocket.length===2) return rocket;

  return null;
}

function findCandidates(cards, lastHT) {
  const { type, rank, n, k } = lastHT;
  const sorted = sortCards(cards);
  const freq = getFreq(cards);
  const results = [];

  if (type === 'single') {
    sorted.filter(c=>c.numVal>rank).forEach(c => results.push([c]));
  } else if (type === 'pair') {
    const pairs = Object.entries(freq).filter(([v,cnt])=>cnt>=2 && +v>rank);
    pairs.forEach(([v])=>{
      const cs = cards.filter(c=>c.numVal===+v).slice(0,2);
      results.push(cs);
    });
  } else if (type === 'triple') {
    const trips = Object.entries(freq).filter(([v,cnt])=>cnt>=3 && +v>rank);
    trips.forEach(([v])=>{
      const cs = cards.filter(c=>c.numVal===+v).slice(0,3);
      results.push(cs);
    });
  } else if (type === 'triple_single') {
    const trips = Object.entries(freq).filter(([v,cnt])=>cnt>=3 && +v>rank);
    trips.forEach(([v])=>{
      const triCards = cards.filter(c=>c.numVal===+v).slice(0,3);
      const kicker = cards.find(c=>c.numVal!==+v);
      if (kicker) results.push([...triCards, kicker]);
    });
  } else if (type === 'triple_pair') {
    const trips = Object.entries(freq).filter(([v,cnt])=>cnt>=3 && +v>rank);
    trips.forEach(([v])=>{
      const triCards = cards.filter(c=>c.numVal===+v).slice(0,3);
      const pairEntry = Object.entries(freq).find(([pv,pc])=>+pv!==+v && pc>=2);
      if (pairEntry) {
        const pairCards = cards.filter(c=>c.numVal===+pairEntry[0]).slice(0,2);
        results.push([...triCards, ...pairCards]);
      }
    });
  } else if (type === 'straight') {
    // 找所有长度相同且最高牌更大的顺子
    const straights = findAllStraights(cards, n);
    straights.filter(s=>analyzeHand(s).rank>rank).forEach(s=>results.push(s));
  } else if (type === 'double_straight') {
    const ds = findAllDoubleStraights(cards, n/2);
    ds.filter(s=>analyzeHand(s).rank>rank).forEach(s=>results.push(s));
  } else if (type === 'triple_straight') {
    const ts = findAllTripleStraights(cards, n/3);
    ts.filter(s=>analyzeHand(s).rank>rank).forEach(s=>results.push(s));
  } else if (type === 'plane_single' || type === 'plane_pair') {
    // simplified: just try to find one
    const ps = findPlaneWithWings(cards, type, k, rank);
    if (ps) results.push(ps);
  }
  return results;
}

function findAllStraights(cards, len) {
  const vals = [...new Set(cards.map(c=>c.numVal))].filter(v=>v<=14).sort((a,b)=>a-b);
  const results = [];
  for (let i=0; i<=vals.length-len; i++) {
    const seq = vals.slice(i, i+len);
    if (seq.every((v,j)=>j===0||v===seq[j-1]+1)) {
      const cs = seq.map(v=>cards.find(c=>c.numVal===v));
      if (cs.every(Boolean)) results.push(cs);
    }
  }
  return results;
}

function findAllDoubleStraights(cards, pairCount) {
  const freq = getFreq(cards);
  const pairVals = Object.keys(freq).map(Number).filter(v=>v<=14&&freq[v]>=2).sort((a,b)=>a-b);
  const results = [];
  for (let i=0; i<=pairVals.length-pairCount; i++) {
    const seq = pairVals.slice(i, i+pairCount);
    if (seq.every((v,j)=>j===0||v===seq[j-1]+1)) {
      const cs = seq.flatMap(v=>cards.filter(c=>c.numVal===v).slice(0,2));
      results.push(cs);
    }
  }
  return results;
}

function findAllTripleStraights(cards, tripleCount) {
  const freq = getFreq(cards);
  const triVals = Object.keys(freq).map(Number).filter(v=>v<=14&&freq[v]>=3).sort((a,b)=>a-b);
  const results = [];
  for (let i=0; i<=triVals.length-tripleCount; i++) {
    const seq = triVals.slice(i, i+tripleCount);
    if (seq.every((v,j)=>j===0||v===seq[j-1]+1)) {
      const cs = seq.flatMap(v=>cards.filter(c=>c.numVal===v).slice(0,3));
      results.push(cs);
    }
  }
  return results;
}

function findPlaneWithWings(cards, type, k, minRank) {
  const freq = getFreq(cards);
  const triVals = Object.keys(freq).map(Number).filter(v=>v<=14&&freq[v]>=3).sort((a,b)=>a-b);
  for (let s=0; s<triVals.length; s++) {
    let len = 1;
    while (s+len<triVals.length && triVals[s+len]===triVals[s+len-1]+1) len++;
    if (len < k) continue;
    const pv = triVals.slice(s, s+k);
    if (pv[k-1] <= minRank) continue;
    const triCards = pv.flatMap(v=>cards.filter(c=>c.numVal===v).slice(0,3));
    const remaining = cards.filter(c=>!triCards.includes(c));
    if (type==='plane_single' && remaining.length >= k) return [...triCards, ...remaining.slice(0,k)];
    if (type==='plane_pair') {
      const rFreq = getFreq(remaining);
      const pairVals = Object.keys(rFreq).map(Number).filter(v=>rFreq[v]>=2);
      if (pairVals.length >= k) {
        const pairCards = pairVals.slice(0,k).flatMap(v=>remaining.filter(c=>c.numVal===v).slice(0,2));
        return [...triCards, ...pairCards];
      }
    }
  }
  return null;
}

function findBestStraight(cards) {
  const vals = [...new Set(cards.map(c=>c.numVal))].filter(v=>v<=14).sort((a,b)=>a-b);
  let best = null;
  for (let i=0; i<vals.length; i++) {
    let len = 1;
    while (i+len<vals.length && vals[i+len]===vals[i+len-1]+1) len++;
    if (len >= 5) {
      const seq = vals.slice(i, i+len);
      const cs = seq.map(v=>cards.find(c=>c.numVal===v));
      if (!best || cs.length > best.length) best = cs;
    }
  }
  return best;
}

function findBestDoubleStraight(cards) {
  const freq = getFreq(cards);
  const pVals = Object.keys(freq).map(Number).filter(v=>v<=14&&freq[v]>=2).sort((a,b)=>a-b);
  let best = null;
  for (let i=0; i<pVals.length; i++) {
    let len = 1;
    while (i+len<pVals.length && pVals[i+len]===pVals[i+len-1]+1) len++;
    if (len >= 3) {
      const seq = pVals.slice(i, i+len);
      const cs = seq.flatMap(v=>cards.filter(c=>c.numVal===v).slice(0,2));
      if (!best || cs.length > best.length) best = cs;
    }
  }
  return best;
}

function findTriplePlay(cards, minRank) {
  const freq = getFreq(cards);
  const sorted = sortCards(cards);
  for (const c of sorted) {
    if (freq[c.numVal] >= 3 && (minRank===null || c.numVal > minRank)) {
      const tri = cards.filter(x=>x.numVal===c.numVal).slice(0,3);
      const kicker = cards.find(x=>x.numVal!==c.numVal);
      if (kicker) return [...tri, kicker];
      return tri;
    }
  }
  return null;
}

function findBomb(cards) {
  const freq = getFreq(cards);
  const sorted = sortCards(cards);
  for (const c of sorted) {
    if (freq[c.numVal] === 4) return cards.filter(x=>x.numVal===c.numVal);
  }
  return null;
}

// ---------- 积分计算 ----------
function calcScores(winnerIdx) {
  const multiplier = Math.pow(2, G.bombCount) * G.baseScore;
  const isLandlordWin = G.players[winnerIdx].isLandlord;

  const prev0 = G.players[0].score;
  if (isLandlordWin) {
    G.players[0].score += (G.players[0].isLandlord ? 2 : -1) * multiplier;
    G.players[1].score += (G.players[1].isLandlord ? 2 : -1) * multiplier;
    G.players[2].score += (G.players[2].isLandlord ? 2 : -1) * multiplier;
  } else {
    G.players[0].score += (G.players[0].isLandlord ? -2 : 1) * multiplier;
    G.players[1].score += (G.players[1].isLandlord ? -2 : 1) * multiplier;
    G.players[2].score += (G.players[2].isLandlord ? -2 : 1) * multiplier;
  }
  G.lastRoundDelta0 = G.players[0].score - prev0;
}

// ---------- 渲染 ----------
function render() {
  renderPlayers();
  renderCenter();
  renderActionBar(G);
  renderScores(G);
  renderPhaseUI();
}

function renderPlayers() {
  G.players.forEach((p, i) => renderPlayerArea(i));
}

function renderPlayerArea(idx) {
  const p = G.players[idx];
  const area = document.getElementById(`player-area-${idx}`);
  if (!area) return;

  // 玩家名称和身份
  const nameEl = area.querySelector('.player-name');
  if (nameEl) {
    nameEl.textContent = p.name;
    nameEl.className = 'player-name' + (p.isLandlord ? ' is-landlord' : '') +
      (G.currentPlayerIdx === idx && G.phase === 'playing' ? ' is-current' : '');
  }

  const identityEl = area.querySelector('.player-identity');
  if (identityEl) {
    if (G.phase === 'playing' || G.phase === 'gameover') {
      identityEl.textContent = p.isLandlord ? '地主' : '农民';
      identityEl.className = 'player-identity ' + (p.isLandlord ? 'landlord-badge' : 'farmer-badge');
    } else {
      identityEl.textContent = '';
    }
  }

  // 手牌
  const handEl = area.querySelector('.hand-cards');
  if (!handEl) return;
  handEl.innerHTML = '';

  if (idx === 0) {
    // 人类玩家：显示牌面
    p.cards.forEach(card => {
      const el = createCardEl(card, true);
      el.addEventListener('click', () => toggleSelectCard(card));
      handEl.appendChild(el);
    });
  } else {
    // AI：显示牌背或计数
    const count = p.cards.length;
    for (let i=0; i<Math.min(count, 20); i++) {
      const el = createCardBack();
      handEl.appendChild(el);
    }
    // 显示牌数
    const countEl = area.querySelector('.card-count');
    if (countEl) countEl.textContent = `${count}张`;
  }
}

function createCardEl(card, selectable) {
  const el = document.createElement('div');
  el.className = 'card' + (card.isRed ? ' card-red' : '') +
    (card.suit==='joker' ? ' card-joker' : '') +
    (selectable && G.selectedCards.some(c=>c.id===card.id) ? ' selected' : '');
  el.dataset.id = card.id;

  if (card.suit === 'joker') {
    el.innerHTML = `<div class="card-joker-content">${card.value}</div>`;
  } else {
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
  }
  return el;
}

function createCardBack() {
  const el = document.createElement('div');
  el.className = 'card card-back';
  el.innerHTML = `<div class="card-back-pattern">🂠</div>`;
  return el;
}

function toggleSelectCard(card) {
  if (G.phase !== 'playing' || G.currentPlayerIdx !== 0) return;
  const idx = G.selectedCards.findIndex(c=>c.id===card.id);
  if (idx >= 0) G.selectedCards.splice(idx, 1);
  else G.selectedCards.push(card);
  renderPlayerArea(0);
  updatePlayBtn();
}

function renderCenter() {
  const centerEl = document.getElementById('center-play-area');
  if (!centerEl) return;

  // 底牌展示
  const bottomEl = document.getElementById('bottom-cards');
  if (bottomEl) {
    if (G.phase === 'playing' || G.phase === 'gameover') {
      bottomEl.innerHTML = '<span class="bottom-label">底牌：</span>';
      G.bottomCards.forEach(c => {
        const el = createCardEl(c, false);
        el.style.transform = 'scale(0.85)';
        bottomEl.appendChild(el);
      });
      bottomEl.style.display = 'flex';
    } else {
      bottomEl.style.display = 'none';
    }
  }

  // 各玩家最后出牌
  [0,1,2].forEach(idx => {
    const el = document.getElementById(`last-play-${idx}`);
    if (!el) return;
    const lp = G.lastPlayInfo;
    if (lp && lp.playerIdx === idx && !lp.isPassed) {
      el.innerHTML = '';
      lp.cards.forEach(c => {
        const ce = createCardEl(c, false);
        ce.style.transform = 'scale(0.75)';
        el.appendChild(ce);
      });
      const typeLabel = document.createElement('div');
      typeLabel.className = 'play-type-label';
      typeLabel.textContent = TYPE_LABEL[lp.handType.type] || '';
      el.appendChild(typeLabel);
    } else if (lp && lp.playerIdx === idx && lp.isPassed) {
      el.innerHTML = '<div class="pass-label">不出</div>';
    } else if (!lp) {
      el.innerHTML = '';
    }
  });
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

function renderScores() {
  G.players.forEach((p, i) => {
    const el = document.getElementById(`score-${i}`);
    if (el) el.textContent = `${p.score >= 0 ? '+' : ''}${p.score}分`;
  });
}

function renderPhaseUI() {
  const biddingUI = document.getElementById('bidding-ui');
  const gameoverUI = document.getElementById('gameover-ui');
  const turnIndicator = document.getElementById('turn-indicator');

  if (biddingUI) {
    biddingUI.style.display = (G.phase==='bidding' && G.currentPlayerIdx===0) ? 'flex' : 'none';
  }

  if (turnIndicator) {
    if (G.phase === 'playing') {
      const p = G.players[G.currentPlayerIdx];
      turnIndicator.textContent = G.currentPlayerIdx===0 ? '轮到你出牌' : `${p.name} 思考中...`;
      turnIndicator.style.display = 'block';
    } else {
      turnIndicator.style.display = 'none';
    }
  }

  if (gameoverUI) {
    if (G.phase === 'gameover') {
      const winner = G.players.find(p=>p.cards.length===0);
      const isLandlordWin = winner?.isLandlord;
      const multiplier = Math.pow(2, G.bombCount);
      gameoverUI.style.display = 'flex';
      const resultEl = document.getElementById('gameover-result');
      if (resultEl) {
        resultEl.textContent = winner
          ? (isLandlordWin ? '🏆 地主胜利！' : '🎉 农民胜利！')
          : '游戏结束';
        resultEl.className = 'gameover-result ' + (isLandlordWin ? 'landlord-win' : 'farmer-win');
      }
      const detailEl = document.getElementById('gameover-detail');
      if (detailEl) {
        detailEl.innerHTML = G.players.map(p =>
          `<div class="score-row">
            <span>${p.name}${p.isLandlord?'（地主）':'（农民）'}</span>
            <span class="${p.score>=0?'positive':'negative'}">${p.score>=0?'+':''}${p.score}分</span>
          </div>`
        ).join('') + `<div class="multiplier-row">炸弹倍率: ×${multiplier}</div>`;
      }
    } else {
      gameoverUI.style.display = 'none';
    }
  }
}

function showMsg(text, duration=1500) {
  let el = document.getElementById('toast-msg');
  if (!el) {
    el = document.createElement('div');
    el.id = 'toast-msg';
    el.className = 'toast-msg';
    document.body.appendChild(el);
  }
  el.textContent = text;
  el.classList.add('show');
  clearTimeout(el._timer);
  el._timer = setTimeout(() => el.classList.remove('show'), duration);
}

// ---------- 打法推荐 ----------
function recommendPlay() {
  if (G.phase !== 'playing' || G.currentPlayerIdx !== 0) return null;
  const myCards   = G.players[0].cards;
  const lastPlay  = G.lastActivePlay;
  const isFree    = !lastPlay || lastPlay.playerIdx === 0;
  return isFree ? _recommendLead(myCards) : _recommendFollow(myCards, lastPlay);
}

function _recommendLead(cards) {
  if (cards.length <= 4) return { cards, reason: '快赢了！打出所有手牌' };

  const sorted = sortCards(cards);
  const freq   = getFreq(cards);

  // 顺子（>=5张）
  const straight = findBestStraight(cards);
  if (straight && straight.length >= 5) {
    const hi = straight[straight.length - 1].value;
    return { cards: straight, reason: `顺子到 ${hi} — 一次清多张` };
  }
  // 连对（>=3对）
  const ds = findBestDoubleStraight(cards);
  if (ds && ds.length >= 6) {
    return { cards: ds, reason: `连对 — 成片清牌` };
  }
  // 三带x
  const triple = findTriplePlay(cards, null);
  if (triple) {
    const ht = analyzeHand(triple);
    const label = TYPE_LABEL[ht.type] || '三带';
    return { cards: triple, reason: `${label} — 带走一张散牌` };
  }
  // 孤牌（没有配对的小牌）
  for (const c of sorted) {
    if (freq[c.numVal] === 1 && c.numVal <= 13) {
      return { cards: [c], reason: `孤牌先清 — 减少累赘` };
    }
  }
  // 最小对子
  for (const c of sorted) {
    if (freq[c.numVal] >= 2 && c.numVal <= 14) {
      const pair = cards.filter(x => x.numVal === c.numVal).slice(0, 2);
      return { cards: pair, reason: `最小对子 — 成对出牌留大牌` };
    }
  }
  // 兜底：最小单张
  return { cards: [sorted[0]], reason: `单张试探` };
}

function _recommendFollow(cards, lastPlay) {
  const lastHT         = lastPlay.handType;
  const lastPlayerIdx  = lastPlay.playerIdx;
  const isMyLandlord   = G.players[0].isLandlord;
  const lastIsTeammate = !isMyLandlord && !G.players[lastPlayerIdx].isLandlord;

  // 队友在领牌 → 不用压
  if (lastIsTeammate) {
    return { cards: null, reason: `队友在领牌，节省好牌` };
  }

  const opponentNearWin = G.players.some((p, i) => i !== 0 && p.cards.length <= 3);
  const candidates = findCandidates(cards, lastHT);

  if (candidates.length > 0) {
    const best  = candidates[0];
    const ht    = analyzeHand(best);
    const label = TYPE_LABEL[ht.type] || '';

    // 用炸弹压非关键局势 → 建议不出
    if ((ht.type === 'bomb' || ht.type === 'rocket') && !opponentNearWin) {
      return { cards: null, reason: `炸弹留着，当前局势不急` };
    }
    return { cards: best, reason: `${label} — 最小压牌` };
  }

  // 无法同类型压过
  if (opponentNearWin) {
    const bomb   = findBomb(cards);
    if (bomb)   return { cards: bomb,   reason: `对手快赢！炸弹出击！` };
    const rocket = cards.filter(c => c.numVal >= 16);
    if (rocket.length === 2) return { cards: rocket, reason: `对手快赢！王炸压制！` };
  }

  return { cards: null, reason: `压不过，建议不出` };
}

// ---------- 公开 API ----------
window.DDZ = {
  initGame,
  bid,
  humanPlay: () => humanPlay(G.selectedCards),
  humanPass,
  selectAll: () => {
    G.selectedCards = [...G.players[0].cards];
    renderPlayerArea(0);
    updatePlayBtn();
  },
  deselectAll: () => {
    G.selectedCards = [];
    renderPlayerArea(0);
    updatePlayBtn();
  },
  setBet: (amt) => { G.betPerPoint = amt; },
  recommendPlay,
  getState: () => G
};
