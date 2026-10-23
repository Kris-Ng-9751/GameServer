# 优化说明

## 新增文件
| 文件 | 作用 |
|---|---|
| `shared.js` | 全站共用：安全存储（隐私模式不再报错）、记录上次游玩、切后台暂停 BGM、图标按钮补 aria-label |
| `shared.css` | 全站共用：键盘焦点环、触屏去延迟/去高亮、减少动态效果、防下拉刷新 |
| `mahjong-fx.css` / `mahjong-fx.js` | 麻将视觉层（牌桌质感、出牌/胡牌动画、纸屑），三人/四人通用 |
| `mahjong-sym4.css` | 仅四人麻将：以牌桌中心对称的布局修正 |

## 修改文件
- **全部 15 个页面**：注入 shared.js / shared.css、theme-color、图标；`<html lang>` 按实际用字统一为 zh-Hans / zh-Hant
- **index.html**：卡片改为自适应网格、修复描述乱折行、新增「繼續上次遊戲」；标题统一
- **mobile.html**：修复引用不存在的 `game.js` → `mahjong4.js`（此前整页无法运行）
- **mahjong3.html**：标题修正、启用视觉层
- **mahjong4.html**：启用对称布局
- **mahjong-core.js**：胡牌判断重写（约快 8 倍，4 万手牌与原算法结果一致）；普通 AI 不再拆对子
- **bgm.mp3**：8.26 MB → 3.99 MB（128 kbps，去掉内嵌封面，时长不变）；`preload="auto"` → `"metadata"`，进页面不再先下载整首

## 未改动（建议后续）
- `mahjong3.js` 与 `mahjong4.js` 约 88% 重复（差异仅 553 行），建议合并为一个按人数参数化的模块
- 各游戏的余额读写仍是各页自己实现，多标签页同时开会互相覆盖（最后写入者生效）
- 页面文字繁简混用，未做转换
