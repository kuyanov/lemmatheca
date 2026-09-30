"use strict";

const dialog = document.getElementById("placeholder-dialog");
const title = document.getElementById("dialog-title");
const description = document.getElementById("dialog-description");
const contributeLink = document.getElementById("contribute-link");
const messages = {
  login: ["Your place in the library.", "Accounts are coming soon. For now, everything in Lemmatheca is open to explore — no login needed."],
  submit: ["There’s room for your ideas.", "Add an entry, improve an explanation, or help prove a result. Contributions and reviews happen in our GitHub repository — the contribution guide will help you get started."],
};

document.querySelectorAll("[data-placeholder]").forEach((button) => {
  button.addEventListener("click", () => {
    [title.textContent, description.textContent] = messages[button.dataset.placeholder];
    contributeLink.hidden = button.dataset.placeholder !== "submit";
    dialog.showModal();
  });
});

dialog.addEventListener("click", (event) => {
  if (event.target !== dialog) return;
  const bounds = dialog.getBoundingClientRect();
  if (event.clientX < bounds.left || event.clientX > bounds.right ||
    event.clientY < bounds.top || event.clientY > bounds.bottom) dialog.close();
});

// Keep the contents and anchor targets below the sticky area/return navigation.
const outline = document.querySelector(".proof-outline");
const entryNavigation = document.querySelector(".entry-navigation-bar");
if (outline) {
  let scheduled = false;
  const fitOutline = () => {
    scheduled = false;
    if (entryNavigation) {
      document.documentElement.style.setProperty(
        "--entry-nav-height", `${entryNavigation.getBoundingClientRect().height}px`);
    }
    const available = window.innerHeight - Math.max(0, outline.getBoundingClientRect().top) - 24;
    outline.style.setProperty("--outline-height", `${Math.max(0, available)}px`);
  };
  const scheduleFit = () => {
    if (!scheduled) {
      scheduled = true;
      requestAnimationFrame(fitOutline);
    }
  };
  window.addEventListener("scroll", scheduleFit, { passive: true });
  window.addEventListener("resize", scheduleFit);
  window.addEventListener("load", scheduleFit);
  if (entryNavigation) new ResizeObserver(scheduleFit).observe(entryNavigation);
  fitOutline();
}
