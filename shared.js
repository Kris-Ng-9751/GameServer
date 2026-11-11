/* shared.js — 全站共用基础层（须在 <head> 最前面同步加载，早于各页面自己的脚本）
   1. 安全存储：隐私模式 / 禁用存储 / file:// 下 localStorage 可能抛错，改为静默降级到内存，避免整页脚本中断
   2. 记录「上次游玩」供大厅高亮
   3. 切到后台自动暂停 BGM，回来再续播
   4. 为只有图标的按钮自动补 aria-label（读屏 / 无障碍）                    */
(function () {
  "use strict";

  /* ── 1) 安全存储 ─────────────────────────────────────────── */
  var mem = {};
  var ok = true;
  try { var k = "__mj_probe__"; localStorage.setItem(k, "1"); localStorage.removeItem(k); } catch (e) { ok = false; }
  var P = Storage.prototype, _get = P.getItem, _set = P.setItem, _del = P.removeItem;
  P.getItem = function (key) {
    try { return _get.call(this, key); } catch (e) { return Object.prototype.hasOwnProperty.call(mem, key) ? mem[key] : null; }
  };
  P.setItem = function (key, val) {
    try { _set.call(this, key, val); } catch (e) { mem[key] = String(val); }
  };
  P.removeItem = function (key) {
    try { _del.call(this, key); } catch (e) { delete mem[key]; }
  };

  /* ── 2) 上次游玩 ─────────────────────────────────────────── */
  var page = (location.pathname.split("/").pop() || "index.html");
  if (page !== "index.html" && /\.html$/.test(page)) {
    try { localStorage.setItem("mj-last-game", page); } catch (e) {}
  }

  /* ── 3) 后台暂停 BGM ─────────────────────────────────────── */
  var resumeBgm = false;
  document.addEventListener("visibilitychange", function () {
    var a = document.getElementById("bgm");
    if (!a) return;
    if (document.hidden) { resumeBgm = !a.paused; if (resumeBgm) a.pause(); }
    else if (resumeBgm) { resumeBgm = false; var p = a.play(); if (p && p.catch) p.catch(function () {}); }
  });

  /* ── 4) 图标按钮补 aria-label ────────────────────────────── */
  function label(root) {
    var list = (root.querySelectorAll ? root.querySelectorAll("button[title]:not([aria-label]),a[title]:not([aria-label])") : []);
    for (var i = 0; i < list.length; i++) list[i].setAttribute("aria-label", list[i].getAttribute("title"));
  }
  document.addEventListener("DOMContentLoaded", function () {
    label(document);
    new MutationObserver(function (ms) {
      for (var i = 0; i < ms.length; i++)
        for (var j = 0; j < ms[i].addedNodes.length; j++)
          if (ms[i].addedNodes[j].nodeType === 1) label(ms[i].addedNodes[j]);
    }).observe(document.body, { childList: true, subtree: true });
  });
})();

/* ══ MJ_UI：全站共用的轻量 UI ═════════════════════════════════
   MJ_UI.toast(msg)           非阻塞提示，替代会卡住页面的 alert()
   MJ_UI.relief({balance,min,idle,refill})
        余额低于最小下注额、且当前处于「空闲」(没有进行中的牌局/旋转) 时，
        在页面底部显示救济金横幅；点击后调用 refill(10000)。 */
(function () {
  "use strict";
  var host, bar, dismissedAt = null;
  function ensure() {
    if (host) return;
    host = document.createElement("div");
    host.setAttribute("aria-live", "polite");
    host.style.cssText = "position:fixed;left:50%;bottom:calc(18px + env(safe-area-inset-bottom,0px));transform:translateX(-50%);z-index:99999;display:flex;flex-direction:column;align-items:center;gap:8px;pointer-events:none;max-width:92vw";
    document.body.appendChild(host);
  }
  function el(css, text) { var e = document.createElement("div"); e.style.cssText = css; if (text) e.textContent = text; return e; }
  var CARD = "pointer-events:auto;background:rgba(14,24,34,.94);color:#f0e6c8;border:1px solid rgba(255,210,74,.45);border-radius:14px;padding:10px 16px;font:600 14px/1.5 system-ui,'PingFang TC','Microsoft JhengHei',sans-serif;box-shadow:0 10px 30px rgba(0,0,0,.5);backdrop-filter:blur(8px)";
  var MJ_UI = {
    toast: function (msg, ms) {
      if (!document.body) { return; }
      ensure();
      var t = el(CARD + ";transition:opacity .25s,transform .25s;opacity:0;transform:translateY(8px)", String(msg));
      host.appendChild(t);
      requestAnimationFrame(function () { t.style.opacity = "1"; t.style.transform = "none"; });
      setTimeout(function () { t.style.opacity = "0"; setTimeout(function () { t.remove(); }, 260); }, ms || 2600);
    },
    relief: function (o) {
      if (!document.body) return;
      var need = o.balance < (o.min || 1) && o.idle !== false;
      if (!need) { if (bar) { bar.remove(); bar = null; } if (o.balance >= (o.min || 1)) dismissedAt = null; return; }
      if (bar || dismissedAt === o.balance) return;
      ensure();
      bar = el(CARD + ";display:flex;align-items:center;gap:12px;flex-wrap:wrap;justify-content:center");
      bar.appendChild(el("", "💸 餘額不足（剩 " + o.balance.toLocaleString() + "），無法繼續下注"));
      var b = document.createElement("button");
      b.textContent = "領取救濟金 10,000";
      b.style.cssText = "cursor:pointer;border:0;border-radius:999px;padding:7px 16px;font:800 13px system-ui,sans-serif;color:#2b1c00;background:linear-gradient(135deg,#ffe066,#ffb300)";
      b.onclick = function () { bar.remove(); bar = null; dismissedAt = null; o.refill(10000); };
      var x = document.createElement("button");
      x.textContent = "×"; x.setAttribute("aria-label", "關閉");
      x.style.cssText = "cursor:pointer;border:0;background:transparent;color:#9fb4b1;font:700 18px/1 system-ui,sans-serif;padding:0 4px";
      x.onclick = function () { dismissedAt = o.balance; bar.remove(); bar = null; };
      bar.appendChild(b); bar.appendChild(x); host.appendChild(bar);
    }
  };
  window.MJ_UI = MJ_UI;
})();
