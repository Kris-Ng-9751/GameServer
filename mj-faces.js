/* mj-faces.js — 四人麻将牌面重制（台麻手游风）。
   只替换牌面的「画法」：萬/筒/條/風箭/飛 全部改为矢量图（viewBox 100×136），
   牌面多大图就等比缩放，字号/图案不再因场景不同而错位。规则与 DOM 类名不变。
   必须在 mahjong4.js 之后加载。 */
(function () {
  "use strict";
  if (typeof window.renderTile !== "function") return;
  const NS = "http://www.w3.org/2000/svg";
  const G = "#16863f", GD = "#0b5226", B = "#1f5fb8", BD = "#12397a", R = "#cc1d22", RD = "#7d0c10", INK = "#17171a";
  const FONT = '"Noto Sans TC","Noto Sans CJK TC","PingFang TC","Microsoft JhengHei","Heiti TC","Hiragino Sans",sans-serif';
  const NUM = ["一", "二", "三", "四", "五", "六", "七", "八", "九"];
  const HONOR = ["東", "南", "西", "北", "中", "發", "白"];

  /* ── 筒：同心圆点 ── */
  const dot = (x, y, r, c) =>
    `<circle cx="${x}" cy="${y}" r="${r}" fill="${c}"/><circle cx="${x}" cy="${y}" r="${r * 0.76}" fill="#fff"/>` +
    `<circle cx="${x}" cy="${y}" r="${r * 0.62}" fill="${c}"/><circle cx="${x}" cy="${y}" r="${r * 0.32}" fill="#fff"/>` +
    `<circle cx="${x}" cy="${y}" r="${r * 0.18}" fill="${c}"/>`;
  function pinBig() {
    let s = `<circle cx="50" cy="68" r="39" fill="${R}"/><circle cx="50" cy="68" r="34" fill="#fff"/><circle cx="50" cy="68" r="30" fill="${G}"/>`;
    for (let i = 0; i < 12; i++) {
      const a = (i * Math.PI) / 6;
      s += `<circle cx="${50 + 24 * Math.cos(a)}" cy="${68 + 24 * Math.sin(a)}" r="3" fill="#fff"/>`;
    }
    return s + `<circle cx="50" cy="68" r="17" fill="#fff"/><circle cx="50" cy="68" r="14" fill="${B}"/><circle cx="50" cy="68" r="7" fill="#fff"/><circle cx="50" cy="68" r="3.5" fill="${R}"/>`;
  }
  const PIN = {
    2: [[50, 36, 22, G], [50, 100, 22, B]],
    3: [[27, 30, 18, B], [50, 68, 18, R], [73, 106, 18, G]],
    4: [[30, 38, 19, B], [70, 38, 19, G], [30, 98, 19, G], [70, 98, 19, B]],
    5: [[28, 34, 17, B], [72, 34, 17, G], [50, 68, 17, R], [28, 102, 17, G], [72, 102, 17, B]],
    6: [[30, 28, 16, G], [70, 28, 16, G], [30, 68, 16, R], [70, 68, 16, R], [30, 108, 16, R], [70, 108, 16, R]],
    7: [[26, 22, 12.5, G], [50, 34, 12.5, G], [74, 46, 12.5, G], [32, 82, 14.5, R], [68, 82, 14.5, R], [32, 112, 14.5, R], [68, 112, 14.5, R]],
    8: [[32, 21, 13, B], [68, 21, 13, B], [32, 50, 13, B], [68, 50, 13, B], [32, 80, 13, B], [68, 80, 13, B], [32, 109, 13, B], [68, 109, 13, B]],
    9: [[24, 28, 14, G], [50, 28, 14, G], [76, 28, 14, G], [24, 68, 14, R], [50, 68, 14, R], [76, 68, 14, R], [24, 108, 14, B], [50, 108, 14, B], [76, 108, 14, B]],
  };
  const pinFace = (n) => (n === 1 ? pinBig() : PIN[n].map((p) => dot(p[0], p[1], p[2], p[3])).join(""));

  /* ── 條：竹节 ── */
  function stick(x, y, w, h, c) {
    w *= 1.3; h *= 1.08;
    const d = c === R ? RD : c === B ? BD : GD;
    const x0 = x - w / 2, y0 = y - h / 2;
    return `<rect x="${x0}" y="${y0}" width="${w}" height="${h}" rx="${w * 0.42}" fill="${c}" stroke="${d}" stroke-width="1.4"/>` +
      `<rect x="${x0 + w * 0.16}" y="${y0 + h * 0.08}" width="${w * 0.16}" height="${h * 0.84}" rx="${w * 0.08}" fill="#fff" opacity=".28"/>` +
      `<path d="M${x0 + 1} ${y - h * 0.17}H${x0 + w - 1}M${x0 + 1} ${y + h * 0.17}H${x0 + w - 1}" stroke="#fff" stroke-width="2.2" opacity=".9"/>`;
  }
  function bird() {
    return `<g>` +
      `<path d="M50 62 C20 55 12 30 20 14 C30 30 40 40 50 54Z" fill="${R}" stroke="${RD}" stroke-width="1"/>` +
      `<path d="M50 62 C80 55 88 30 80 14 C70 30 60 40 50 54Z" fill="${B}" stroke="${BD}" stroke-width="1"/>` +
      `<path d="M50 60 C42 44 44 28 50 16 C56 28 58 44 50 60Z" fill="${G}" stroke="${GD}" stroke-width="1"/>` +
      `<ellipse cx="50" cy="86" rx="20" ry="28" fill="${G}" stroke="${GD}" stroke-width="1.6"/>` +
      `<ellipse cx="50" cy="92" rx="11" ry="17" fill="#e8f5e0" opacity=".85"/>` +
      `<circle cx="50" cy="56" r="11" fill="${G}" stroke="${GD}" stroke-width="1.6"/>` +
      `<path d="M50 40 L46 46 M50 40 L54 46 M50 40 L50 45" stroke="${R}" stroke-width="2.4" stroke-linecap="round"/>` +
      `<circle cx="54" cy="54" r="2.6" fill="#fff"/><circle cx="54.6" cy="54" r="1.2" fill="${INK}"/>` +
      `<path d="M58 58 L68 62 L58 64Z" fill="#e8a020" stroke="#9a6410" stroke-width=".8"/>` +
      `<path d="M44 112 L40 128 M56 112 L60 128" stroke="#9a6410" stroke-width="2.6" stroke-linecap="round"/></g>`;
  }
  const SOU = {
    2: [[50, 36, 12, 42, G], [50, 100, 12, 42, B]],
    3: [[50, 34, 13, 44, G], [32, 98, 13, 44, B], [68, 98, 13, 44, B]],
    4: [[32, 36, 13, 44, G], [68, 36, 13, 44, B], [32, 100, 13, 44, B], [68, 100, 13, 44, G]],
    5: [[28, 34, 13, 38, G], [72, 34, 13, 38, B], [50, 68, 13, 38, R], [28, 102, 13, 38, B], [72, 102, 13, 38, G]],
    6: [[26, 38, 14, 46, G], [50, 38, 14, 46, G], [74, 38, 14, 46, G], [26, 98, 14, 46, B], [50, 98, 14, 46, B], [74, 98, 14, 46, B]],
    7: [[50, 24, 13, 30, R], [26, 66, 13, 36, G], [50, 66, 13, 36, G], [74, 66, 13, 36, G], [26, 106, 13, 36, B], [50, 106, 13, 36, B], [74, 106, 13, 36, B]],
    8: [[20, 36, 12, 44, G], [40, 36, 12, 44, G], [60, 36, 12, 44, G], [80, 36, 12, 44, G], [20, 100, 12, 44, B], [40, 100, 12, 44, B], [60, 100, 12, 44, B], [80, 100, 12, 44, B]],
    9: [[26, 26, 13, 34, G], [50, 26, 13, 34, R], [74, 26, 13, 34, B], [26, 68, 13, 34, G], [50, 68, 13, 34, R], [74, 68, 13, 34, B], [26, 110, 13, 34, G], [50, 110, 13, 34, R], [74, 110, 13, 34, B]],
  };
  const souFace = (n) => (n === 1 ? bird() : SOU[n].map((p) => stick(p[0], p[1], p[2], p[3], p[4])).join(""));

  /* ── 文字牌 ── */
  const txt = (ch, x, y, size, fill, sw = 1.6) =>
    `<text x="${x}" y="${y}" text-anchor="middle" font-family='${FONT}' font-weight="900" font-size="${size}" fill="${fill}" stroke="${fill}" stroke-width="${sw}" stroke-linejoin="round">${ch}</text>`;
  const manFace = (n) => txt(NUM[n - 1], 50, 60, 56, INK, 1.2) + txt("萬", 50, 116, 50, R, 0.5);
  function honorFace(n) {
    if (n === 7) {
      return `<rect x="14" y="20" width="72" height="96" rx="9" fill="none" stroke="${B}" stroke-width="6"/>` +
        `<rect x="24" y="30" width="52" height="76" rx="4" fill="none" stroke="${B}" stroke-width="2" opacity=".55"/>`;
    }
    const col = n <= 4 ? INK : n === 5 ? R : G;
    return txt(HONOR[n - 1], 50, 96, 80, col);
  }
  const feiFace = () =>
    `<circle cx="50" cy="68" r="38" fill="#ffd45a" stroke="#b9801a" stroke-width="3"/><circle cx="50" cy="68" r="31" fill="none" stroke="#fff" stroke-width="1.5" opacity=".8"/>` +
    txt("飛", 50, 90, 56, RD);

  function face(code) {
    const s = code[0], n = parseInt(code.slice(1), 10);
    let body = "";
    if (s === "M") body = manFace(n);
    else if (s === "P") body = pinFace(n);
    else if (s === "S") body = souFace(n);
    else if (s === "Z") body = honorFace(n);
    else if (s === "H") body = feiFace();
    else return null;
    const svg = document.createElementNS(NS, "svg");
    svg.setAttribute("viewBox", "0 0 100 136");
    svg.setAttribute("preserveAspectRatio", "xMidYMid meet");
    svg.setAttribute("class", "mjface");
    svg.setAttribute("aria-hidden", "true");
    svg.innerHTML = body;
    return svg;
  }

  const orig = window.renderTile;
  window.renderTile = function (tileCode, isPlayer) {
    const el = orig(tileCode, isPlayer);
    try {
      const f = face(String(tileCode));
      if (f) { el.textContent = ""; el.appendChild(f); el.classList.add("mjf"); }
    } catch (e) { /* 出错则保留原牌面 */ }
    return el;
  };
  window.MJ_FACE = face;
})();
