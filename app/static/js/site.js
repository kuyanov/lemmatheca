"use strict";

const dialog = document.getElementById("placeholder-dialog");
const title = document.getElementById("dialog-title");
const description = document.getElementById("dialog-description");
const messages = {
  login: ["Your place in the library.", "Accounts are coming soon. For now, everything in the library is open to explore — no login needed."],
  submit: ["There’s room for your ideas.", "Proof submissions are coming soon. You’ll be able to share an argument and help the library grow. This preview does not collect or submit anything."],
};

document.querySelectorAll("[data-placeholder]").forEach((button) => {
  button.addEventListener("click", () => {
    [title.textContent, description.textContent] = messages[button.dataset.placeholder];
    dialog.showModal();
  });
});

dialog.addEventListener("click", (event) => {
  if (event.target !== dialog) return;
  const bounds = dialog.getBoundingClientRect();
  if (event.clientX < bounds.left || event.clientX > bounds.right ||
      event.clientY < bounds.top || event.clientY > bounds.bottom) dialog.close();
});
