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
