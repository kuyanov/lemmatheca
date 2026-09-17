"use strict";

document.querySelectorAll("[data-math]").forEach((element) => {
  renderMathInElement(element, {
    delimiters: [
      { left: "\\[", right: "\\]", display: true },
      { left: "\\(", right: "\\)", display: false },
    ],
    throwOnError: true,
    trust: false,
    strict: "error",
  });
});
