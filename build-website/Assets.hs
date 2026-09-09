{-# LANGUAGE QuasiQuotes #-}

-- | Stylesheet, script, and favicon for the static site. Semantic colour is
-- defined once as custom properties and reused on every page.
module Assets
  ( css
  , js
  , faviconSvg
  ) where

import Data.Text (Text)
import Text.RawString.QQ (r)

css :: Text
css = [r|
:root {
  --bg: #ffffff;
  --fg: #111111;
  --muted: #333333;
  --card: #ffffff;
  --accent: #0000aa;
  --line: #111111;
  --lp-kw: #9b0000;
  --lp-binder: #6b00a0;
  --lp-var: #005500;
  --lp-const: #111111;
  --lp-op: #8a4000;
  --lp-pred: #003399;
  --lp-ty: #004d4d;
  --lp-tyvar: #005500;
  --lp-kind: #9b0000;
  --lp-lit: #000000;
  --lp-pi: #9b0000;
  --lp-impl: #8a4000;
  --lp-punct: #111111;
  --lp-comment: #444444;
  --lp-key: #003399;
  --lp-val: #111111;
  --lp-mod: #003399;
}
* { box-sizing: border-box; border-radius: 0; }
html { font-size: 18px; }
body {
  margin: 0;
  font-family: "STIX Two Text", "STIX Two Math", "Latin Modern Roman", "Cambria Math", Palatino, "Times New Roman", serif;
  background: var(--bg);
  color: var(--fg);
  line-height: 1.5;
  border-top: 2px solid var(--line);
}
::selection { background: #111111; color: #ffffff; }
a { color: var(--accent); text-decoration: none; }
a:hover { text-decoration: underline; }
header, main, footer { max-width: 52rem; margin: 0 auto; padding: 1.25rem 1rem; }
header { border-bottom: 1px solid var(--line); }
footer { border-top: 1px solid var(--line); color: var(--muted); font-size: 0.9rem; }
nav a { margin-right: 1rem; }
h1, h2 {
  font-family: "STIX Two Text", "STIX Two Math", Palatino, serif;
  font-weight: 600;
  letter-spacing: 0;
  margin: 1.2rem 0 0.5rem;
}
.muted { color: var(--muted); }
.cards { display: grid; gap: 0; }
.card {
  background: var(--card);
  border: 1px solid var(--line);
  border-top: 0;
  padding: 0.85rem 1rem;
}
.cards .card:first-child { border-top: 1px solid var(--line); }
.card h2 { margin: 0 0 0.35rem; font-size: 1.15rem; }
.tags span {
  display: inline-block;
  font-size: 0.75rem;
  color: var(--fg);
  border: 1px solid var(--line);
  padding: 0 0.4rem;
  margin-right: 0.3rem;
}
pre.src {
  font-family: "STIX Two Math", "Latin Modern Mono", "Cambria Math", ui-monospace, monospace;
  font-size: 0.95rem;
  background: #fff;
  color: var(--fg);
  padding: 0.85rem 1rem;
  overflow: auto;
  line-height: 1.45;
  border: 1px solid var(--line);
  margin: 1rem 0;
  font-variant-ligatures: none;
}
code {
  font-family: "STIX Two Math", "Latin Modern Mono", ui-monospace, monospace;
  font-variant-ligatures: none;
}
.lp-kw { color: var(--lp-kw); font-weight: 600; }
.lp-binder { color: var(--lp-binder); font-weight: 600; }
.lp-var { color: var(--lp-var); font-style: italic; }
.lp-const { color: var(--lp-const); }
.lp-op { color: var(--lp-op); }
.lp-pred { color: var(--lp-pred); font-weight: 600; }
.lp-ty { color: var(--lp-ty); }
.lp-tyvar { color: var(--lp-tyvar); font-style: italic; }
.lp-kind { color: var(--lp-kind); }
.lp-lit { color: var(--lp-lit); }
.lp-pi { color: var(--lp-pi); font-weight: 600; }
.lp-impl { color: var(--lp-impl); font-weight: 600; }
.lp-punct { color: var(--lp-punct); }
.lp-comment { color: var(--lp-comment); font-style: italic; }
.lp-key { color: var(--lp-key); font-weight: 600; font-style: normal; }
.lp-val { color: var(--lp-val); font-style: italic; }
.lp-mod { color: var(--lp-mod); font-weight: 600; }
span[data-tip] { cursor: help; }
span[data-tip]:hover, span[data-tip]:focus {
  outline: 1px solid var(--line);
  background: #f4f4f4;
}
#tip {
  position: fixed;
  max-width: 24rem;
  padding: 0.4rem 0.55rem;
  background: #fff;
  color: var(--fg);
  border: 1px solid var(--line);
  font-family: "STIX Two Text", Palatino, serif;
  font-size: 0.9rem;
  pointer-events: none;
  z-index: 20;
}
.legend { display: flex; flex-wrap: wrap; gap: 0.5rem; font-size: 0.85rem; }
.legend i { font-style: normal; border: 1px solid var(--line); padding: 0 0.35rem; }
|]

js :: Text
js = [r|
const tip = document.getElementById("tip");
function show(e) {
  const t = e.currentTarget.getAttribute("data-tip");
  if (!t || !tip) return;
  tip.textContent = t;
  tip.hidden = false;
  const r = e.currentTarget.getBoundingClientRect();
  tip.style.left = Math.min(r.left, window.innerWidth - 280) + "px";
  tip.style.top = (r.bottom + 8) + "px";
}
function hide() { if (tip) tip.hidden = true; }
document.querySelectorAll("[data-tip]").forEach((el) => {
  el.addEventListener("mouseenter", show);
  el.addEventListener("focus", show);
  el.addEventListener("mouseleave", hide);
  el.addEventListener("blur", hide);
});
|]

faviconSvg :: Text
faviconSvg = [r|
<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 32 32">
  <rect x="0.5" y="0.5" width="31" height="31" fill="#ffffff" stroke="#111111" stroke-width="1"/>
  <text x="4" y="23" font-size="16" fill="#111111" font-family="STIX Two Math, Cambria Math, Times New Roman, serif">λΠ</text>
</svg>
|]
