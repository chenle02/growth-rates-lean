// Fold and copy code blocks on the documentation site.
// 1. Every Lean code block (```lean in Markdown, <pre><code class="language-lean"> in HTML)
//    is wrapped in a <details> element: open when it has at most OPEN_MAX lines, folded
//    otherwise. The summary says how many lines it has. A block already inside a
//    <details> (for example a hand-written "Lean statement" fold) is left as it is.
// 2. Every <pre> block gets a "Copy" button that copies the exact text of the block.
//    Pages built by MkDocs Material with content.code.copy already have one; they are skipped.
// The generated Markdown is not modified, so `lean-pkg page --check` stays valid.
// No network access, no dependencies; the copied text is read with textContent.
(function () {
  var OPEN_MAX = 15;

  function copyText(text, button) {
    function done(ok) {
      button.textContent = ok ? "Copied" : "Copy failed";
      setTimeout(function () { button.textContent = "Copy"; }, 1500);
    }
    if (navigator.clipboard && window.isSecureContext) {
      navigator.clipboard.writeText(text).then(function () { done(true); }, function () { done(fallback(text)); });
      return;
    }
    done(fallback(text));
  }

  function fallback(text) {
    var area = document.createElement("textarea");
    area.value = text;
    area.setAttribute("readonly", "");
    area.style.position = "fixed";
    area.style.opacity = "0";
    document.body.appendChild(area);
    area.select();
    var ok = false;
    try { ok = document.execCommand("copy"); } catch (e) { ok = false; }
    document.body.removeChild(area);
    return ok;
  }

  function addCopyButtons(root) {
    root.querySelectorAll("pre").forEach(function (pre) {
      if (pre.dataset.copyDone) return;
      pre.dataset.copyDone = "1";
      if (pre.querySelector(".md-clipboard") || (pre.parentNode && pre.parentNode.querySelector && pre.parentNode.querySelector(":scope > .md-clipboard"))) return;
      var wrap = document.createElement("div");
      wrap.className = "code-wrap";
      pre.parentNode.insertBefore(wrap, pre);
      wrap.appendChild(pre);
      var button = document.createElement("button");
      button.type = "button";
      button.className = "code-copy";
      button.textContent = "Copy";
      button.setAttribute("aria-label", "Copy this code block");
      button.addEventListener("click", function () {
        var code = pre.querySelector("code") || pre;
        copyText(code.textContent.replace(/\n$/, ""), button);
      });
      wrap.appendChild(button);
    });
  }

  function foldLeanBlocks(root) {
    var codes = root.querySelectorAll("pre > code.language-lean, pre > code.language-lean4, div.language-lean pre > code, div.language-lean4 pre > code");
    codes.forEach(function (code) {
      var box = code.closest("div.language-lean, div.language-lean4, div.highlight") || code.closest("pre");
      if (!box || box.dataset.foldDone) return;
      box.dataset.foldDone = "1";
      if (box.closest("details")) return;
      var lines = code.textContent.replace(/\n$/, "").split("\n").length;
      var details = document.createElement("details");
      details.className = "lean-fold";
      if (lines <= OPEN_MAX) details.open = true;
      var summary = document.createElement("summary");
      summary.textContent = "Lean statement (" + lines + (lines === 1 ? " line)" : " lines)");
      box.parentNode.insertBefore(details, box);
      details.appendChild(summary);
      details.appendChild(box);
    });
  }

  function run() {
    var root = document.querySelector("main") || document.body;
    foldLeanBlocks(root);
    addCopyButtons(root);
  }

  window.codeBlocks = { run: run };
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", run);
  else run();
  // MkDocs Material instant navigation: run again on every page change.
  if (typeof document$ !== "undefined") document$.subscribe(function () { run(); });
})();
