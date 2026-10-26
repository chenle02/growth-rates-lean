// Typeset mathematics on the documentation site.
// 1. TeX statements that lean-pkg writes as ```latex code blocks (docs/verification.md,
//    docs/coverage.md) are shown typeset, with the exact TeX source kept under a toggle.
//    The generated Markdown is not modified, so `lean-pkg page --check` stays valid.
// 2. GitHub-flavoured math in the hand-written pages: $`...`$ inline (rendered by Jekyll as a
//    code span between two dollar signs) and ```math display blocks are converted to MathJax
//    input in the browser, so one Markdown source reads correctly on GitHub and on this site.
// 3. Inline $...$ / \(...\) and display $$...$$ / \[...\] elsewhere on a page are typeset.
// 4. A statement MathJax cannot typeset (a whole LaTeX excerpt with \begin{lemma}, ...)
//    keeps its exact TeX source, shown unfolded, so a reader never sees an error box.
// MathJax never touches <pre>/<code>, so Lean code stays literal. \require and the html
// extension (\href, \class, ...) are disabled: statement text cannot add links or markup.
(function () {
  function convertTexBlocks(root) {
    var codes = (root || document).querySelectorAll("pre > code.language-latex, div.language-latex pre > code");
    codes.forEach(function (code) {
      var box = code.closest("div.language-latex") || code.closest("pre");
      if (!box || box.dataset.texDone) return;
      box.dataset.texDone = "1";
      var shown = document.createElement("div");
      shown.className = "tex-statement";
      shown.textContent = code.textContent;          // text node: no HTML is interpreted
      var details = document.createElement("details");
      details.className = "tex-source";
      var summary = document.createElement("summary");
      summary.textContent = "TeX source";
      box.parentNode.insertBefore(shown, box);
      box.parentNode.insertBefore(details, box);
      details.appendChild(summary);
      details.appendChild(box);
    });
  }
  function convertGithubMath(root) {
    // ```math blocks: display math
    (root || document).querySelectorAll("div.language-math pre > code, pre > code.language-math").forEach(function (code) {
      var box = code.closest("div.language-math") || code.closest("pre");
      if (!box || box.dataset.texDone) return;
      box.dataset.texDone = "1";
      var shown = document.createElement("div");
      shown.className = "tex-display";
      shown.textContent = "\\[" + code.textContent.trim() + "\\]";
      box.parentNode.replaceChild(shown, box);
    });
    // $`...`$ inline: a code span whose neighbours are text ending and starting with a dollar sign
    (root || document).querySelectorAll("code").forEach(function (code) {
      if (code.closest("pre")) return;
      var before = code.previousSibling, after = code.nextSibling;
      if (!before || !after || before.nodeType !== 3 || after.nodeType !== 3) return;
      if (before.data.slice(-1) !== "$" || after.data.charAt(0) !== "$") return;
      before.data = before.data.slice(0, -1);
      after.data = after.data.slice(1);
      code.parentNode.replaceChild(document.createTextNode("\\(" + code.textContent + "\\)"), code);
    });
  }
  function fallBackToSource() {
    document.querySelectorAll(".tex-statement").forEach(function (shown) {
      if (!shown.querySelector("mjx-merror")) return;
      var details = shown.nextElementSibling;
      if (details && details.classList.contains("tex-source")) details.open = true;
      shown.remove();
    });
  }
  // A formula wider than its column gets .mjx-wide (site.css), so it scrolls inside its own box
  // instead of widening the whole page on a narrow screen.
  function markWideMath() {
    document.querySelectorAll("mjx-container").forEach(function (m) {
      m.classList.remove("mjx-wide");
      var col = m.parentElement && m.parentElement.closest("p, li, td, th, dd, blockquote, section, article, main, div");
      if (col && m.getBoundingClientRect().width > col.clientWidth + 1) m.classList.add("mjx-wide");
    });
  }
  window.texBlocks = { convert: convertTexBlocks };
  window.MathJax = {
    tex: {
      inlineMath: [["$", "$"], ["\\(", "\\)"]],
      displayMath: [["$$", "$$"], ["\\[", "\\]"]],
      processEscapes: true,
      packages: { "[-]": ["require", "autoload"] },
      macros: { label: ["", 1] }   // LaTeX labels repeat across excerpts; they are not shown
    },
    options: { ignoreHtmlClass: "tex-source|tex2jax_ignore" },
    startup: {
      ready: function () {
        convertGithubMath(document);
        convertTexBlocks(document);
        MathJax.startup.defaultReady();
        MathJax.startup.promise.then(fallBackToSource).then(markWideMath);
        var resizeTimer;
        window.addEventListener("resize", function () {
          clearTimeout(resizeTimer);
          resizeTimer = setTimeout(markWideMath, 200);
        });
      }
    }
  };
})();
