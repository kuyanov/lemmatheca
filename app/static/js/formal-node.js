"use strict";

// Line links work even when the source file starts collapsed.
function revealSourceLine(hash) {
  if (!/^#L[1-9]\d*$/.test(hash)) return;
  const line = document.getElementById(hash.slice(1));
  const browser = line?.closest(".node-source-browser");
  if (!browser) return;
  browser.open = true;
  requestAnimationFrame(() => line.scrollIntoView({ block: "center" }));
}

document.addEventListener("click", (event) => {
  const link = event.target.closest(".formal-node-page a[href^='#L']");
  if (link) revealSourceLine(link.getAttribute("href"));
});
window.addEventListener("hashchange", () => revealSourceLine(window.location.hash));
revealSourceLine(window.location.hash);
