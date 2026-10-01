"use strict";

(() => {
  const statistics = JSON.parse(document.getElementById("statistics-data").textContent);
  const history = statistics.history || {};
  const today = Date.now();
  const seriesFor = {
    entries: [["count", "Total entries"], ["verified", "Formalized"]],
    nodes: [["count", "Total nodes"], ["verified", "Verified"]],
    areas: [["count", "Total areas"]],
    contributors: [["count", "Contributors"]],
  };
  const dateLabel = new Intl.DateTimeFormat(undefined, { day: "numeric", month: "short", timeZone: "UTC" });
  const fullDate = new Intl.DateTimeFormat(undefined, { dateStyle: "medium", timeStyle: "short", timeZone: "UTC" });
  const number = new Intl.NumberFormat(undefined, { notation: "compact", maximumFractionDigits: 1 });
  const svgElement = (tag, attrs = {}, text) => {
    const element = document.createElementNS("http://www.w3.org/2000/svg", tag);
    Object.entries(attrs).forEach(([key, value]) => element.setAttribute(key, value));
    if (text !== undefined) element.textContent = text;
    return element;
  };

  document.querySelectorAll(".metric-history-toggle").forEach(button => {
    const card = button.closest(".library-metric");
    const panel = document.getElementById(button.getAttribute("aria-controls"));
    const plot = panel.querySelector(".metric-plot");
    const dates = panel.querySelector(".metric-chart-dates");
    const legend = panel.querySelector(".metric-chart-legend");
    const metric = button.dataset.metric;
    const series = seriesFor[metric].map(([key, label], index) => {
      const points = (history[metric] || [])
        .map(point => ({ time: Date.parse(point.at), count: point[key] }))
        .filter(point => point.time < today);
      const count = statistics[key === "verified" ? `verified_${metric}` : metric];
      // Add the current snapshot for display without changing the saved history.
      if (count != null) points.push({ time: today, count });
      return { label, className: index ? "metric-series-verified" : "metric-series-total", points };
    }).filter(item => item.points.length);

    const draw = () => {
      if (panel.hidden) return;
      plot.replaceChildren();
      dates.replaceChildren();
      legend.replaceChildren();
      if (!series.length) {
        const message = document.createElement("p");
        message.className = "metric-chart-empty";
        message.textContent = "No history recorded yet.";
        plot.append(message);
        return;
      }
      const start = Math.min(...series.map(item => item.points[0].time));
      const end = today;
      // Lay out the captions first so the plot uses the remaining card height.
      [...new Set([dateLabel.format(start), dateLabel.format(end)])].forEach(text => {
        const label = document.createElement("span");
        label.textContent = text;
        dates.append(label);
      });
      series.forEach(item => {
        const label = document.createElement("span");
        label.className = item.className;
        const swatch = document.createElement("i");
        swatch.setAttribute("aria-hidden", "true");
        label.append(swatch, item.label);
        legend.append(label);
      });
      const width = plot.clientWidth;
      const height = plot.clientHeight;
      if (!width || !height) return;
      const maximum = series.reduce((max, item) => item.points.reduce((n, point) => Math.max(n, point.count), max), 1);
      const left = 26, right = width - 4, top = 7, bottom = Math.max(top + 1, height - 5);
      const x = time => end === start ? (left + right) / 2 : left + (time - start) / (end - start) * (right - left);
      const y = count => bottom - count / maximum * (bottom - top);
      const svg = svgElement("svg", { viewBox: `0 0 ${width} ${height}`, role: "img" });
      svg.setAttribute("aria-label", `${button.dataset.label} history. ${series.map(item =>
        `${item.label}: ${item.points[item.points.length - 1].count}`).join(". ")}.`);
      svg.append(svgElement("desc", {}, series.map(item => `${item.label}: ${item.points.map(point =>
        `${point.count} on ${fullDate.format(point.time)} UTC`).join("; ")}`).join(". ")));
      for (const count of [0, maximum]) {
        svg.append(svgElement("line", { x1: left, x2: right, y1: y(count), y2: y(count), class: "metric-chart-grid" }));
        svg.append(svgElement("text", { x: 0, y: y(count) + 3, class: "metric-chart-axis" }, number.format(count)));
      }
      const fills = svgElement("g", { "fill-opacity": 0.12 });
      const lines = svgElement("g", { fill: "none", "stroke-width": 1.6, "stroke-linejoin": "round" });
      svg.append(fills, lines);
      series.forEach(item => {
        const points = item.points.map(point => [x(point.time), y(point.count)]);
        let path = `M${points[0]}`;
        points.slice(1).forEach(([px, py], index) => {
          const [previousX, previousY] = points[index];
          const middle = (previousX + px) / 2;
          // Horizontal handles round each join without overshooting either count.
          path += `C${middle},${previousY} ${middle},${py} ${px},${py}`;
        });
        fills.append(svgElement("path", {
          d: `${path}L${points[points.length - 1][0]},${bottom}L${points[0][0]},${bottom}Z`,
          class: item.className, fill: "currentColor"
        }));
        lines.append(svgElement("path", { d: path, class: item.className, stroke: "currentColor" }));
      });
      plot.append(svg);
    };

    const toggle = show => {
      panel.hidden = !show;
      card.classList.toggle("is-history", show);
      button.setAttribute("aria-expanded", String(show));
      const label = `Show ${button.dataset.label.toLowerCase()} ${show ? "counts" : "history"}`;
      button.setAttribute("aria-label", label);
      button.title = label;
      if (show) draw();
    };
    button.hidden = false;
    button.addEventListener("click", () => toggle(panel.hidden));
    card.addEventListener("keydown", event => {
      if (event.key === "Escape" && !panel.hidden) {
        toggle(false);
        button.focus();
      }
    });
    new ResizeObserver(draw).observe(plot);
  });
})();
