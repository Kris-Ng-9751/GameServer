// mahjong-fx.js — 动画/特效层。必须在 mahjong4.js 之后加载；不修改游戏逻辑，只做观察与包装。
(function () {
  "use strict";
  const reduce = matchMedia("(prefers-reduced-motion: reduce)").matches;

  // 1) 动作大字：写入 data-action 以套用颜色，并加闪光（胡牌时震屏）
  const _show = window.showActionOverlay;
  if (typeof _show === "function") {
    window.showActionOverlay = function (text) {
      const ov = document.getElementById("action-overlay");
      if (ov) ov.dataset.action = text;
      _show.apply(this, arguments);
      if (reduce) return;
      const f = document.createElement("div");
      f.className = "fx-flash";
      document.body.appendChild(f);
      setTimeout(() => f.remove(), 500);
      if (text === "胡") {
        const t = document.getElementById("app");
        if (t) { t.classList.remove("fx-shake"); void t.offsetWidth; t.classList.add("fx-shake"); }
      }
    };
  }

  // 2) 弃牌/摸牌动画：render 每次都会重建 DOM，所以只在「牌数增加」时给新牌加动画，避免重绘时重复播放
  function watchGrow(el, cls, pick) {
    if (!el || reduce) return;
    let n = el.children.length;
    new MutationObserver(() => {
      const c = el.children.length;
      if (c > n) { const t = pick(el); if (t) t.classList.add(cls); }
      n = c;
    }).observe(el, { childList: true });
  }
  ["discard-north", "discard-west", "discard-east", "discard-south"].forEach((id) =>
    watchGrow(document.getElementById(id), "fx-drop", (el) => el.lastElementChild));
  watchGrow(document.getElementById("player-hand"), "fx-draw",
    (el) => el.querySelector(".drawn-tile") || el.lastElementChild);

  // 3) 胡牌五彩纸屑（轻量 canvas，约 2.6 秒）
  function confetti() {
    if (reduce) return;
    const cv = document.createElement("canvas");
    cv.id = "fx-confetti";
    cv.width = innerWidth; cv.height = innerHeight;
    document.body.appendChild(cv);
    const ctx = cv.getContext("2d");
    const colors = ["#f6c847", "#ff6b6b", "#7fe3ff", "#7dffb0", "#c6a7ff", "#fff"];
    const ps = Array.from({ length: 140 }, () => ({
      x: Math.random() * cv.width, y: -20 - Math.random() * cv.height * 0.5,
      vx: (Math.random() - 0.5) * 3, vy: 2 + Math.random() * 4,
      s: 5 + Math.random() * 6, r: Math.random() * 6, vr: (Math.random() - 0.5) * 0.3,
      c: colors[(Math.random() * colors.length) | 0],
    }));
    const t0 = performance.now();
    (function tick(now) {
      const dt = now - t0;
      ctx.clearRect(0, 0, cv.width, cv.height);
      ctx.globalAlpha = Math.max(0, 1 - Math.max(0, dt - 1800) / 800);
      for (const p of ps) {
        p.x += p.vx; p.y += p.vy; p.r += p.vr; p.vy += 0.03;
        ctx.save(); ctx.translate(p.x, p.y); ctx.rotate(p.r);
        ctx.fillStyle = p.c; ctx.fillRect(-p.s / 2, -p.s / 4, p.s, p.s / 2); ctx.restore();
      }
      if (dt < 2600) requestAnimationFrame(tick); else cv.remove();
    })(t0);
  }
  const win = document.getElementById("win-overlay");
  if (win) new MutationObserver(() => { if (!win.classList.contains("hidden")) confetti(); })
    .observe(win, { attributes: true, attributeFilter: ["class"] });
})();
