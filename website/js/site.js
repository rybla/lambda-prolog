
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
