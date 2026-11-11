// mahjong-sym4.js — 仅四人麻将：把四家「玩家资讯」(昵称+分数) 移到各自牌河内侧的中轴线上，
// 围绕中央罗盘形成对等的一圈。DOM 节点只是换了父元素，id/内容不变，游戏逻辑照常按 id 更新。
(function () {
  "use strict";
  ["north", "south", "west", "east"].forEach(function (k) {
    var cell = document.querySelector(".dc-" + k);
    var lab = document.querySelector(".seat-" + k + " > .seat-label");
    if (!cell || !lab) return;
    lab.classList.add("lbl-" + k);
    cell.appendChild(lab);
  });
})();
