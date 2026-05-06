(function () {
  "use strict";

  const STORAGE_KEY = "book-language";

  // ---------------------------------
  // Current language from URL
  // ---------------------------------

  function currentLang() {
    return /\/en\//.test(window.location.pathname) ? "en" : "ru";
  }

  // ---------------------------------
  // Browser language
  // ---------------------------------

  function preferredLang() {
    const langs = navigator.languages || [
      navigator.language || "en",
    ];

    const isRussian = langs.some((lang) =>
      lang.toLowerCase().startsWith("ru")
    );

    return isRussian ? "ru" : "en";
  }

  // ---------------------------------
  // URL conversion
  // ---------------------------------

  function pathForLang(lang) {
    const path = window.location.pathname;

    if (lang === "en") {
      if (/\/en\//.test(path)) {
        return path;
      }

      // /APS/foo → /APS/en/foo
      return path.replace(/^(\/[^\/]+\/)/, "$1en/");
    }

    // lang === "ru"

    // /APS/en/foo → /APS/foo
    return path.replace("/en/", "/");
  }

  // ---------------------------------
  // Switch language manually
  // ---------------------------------

  function switchLanguage() {
    const newLang = currentLang() === "ru" ? "en" : "ru";

    // Save explicit user choice
    localStorage.setItem(STORAGE_KEY, newLang);

    window.location.href =
      pathForLang(newLang) +
      window.location.search +
      window.location.hash;
  }

  // ---------------------------------
  // Automatic language selection
  // ---------------------------------

  function autoSelectLanguage() {
    const current = currentLang();

    // 1. User preference has priority
    let desired = localStorage.getItem(STORAGE_KEY);

    // 2. Otherwise use browser language
    if (!desired) {
      desired = preferredLang();
    }

    // Already correct
    if (desired === current) {
      return;
    }

    // Redirect
    window.location.replace(
      pathForLang(desired) +
      window.location.search +
      window.location.hash
    );
  }

  // ---------------------------------
  // UI
  // ---------------------------------

  function addSwitcher() {
    const lang = currentLang();

    const btn = document.createElement("button");
    btn.id = "language-switcher";

    btn.setAttribute(
      "title",
      lang === "ru"
        ? "Switch to English"
        : "Переключить на русский"
    );

    btn.setAttribute("aria-label", btn.getAttribute("title"));

    const icon = document.createElement("span");
    icon.setAttribute("aria-hidden", "true");
    icon.textContent = lang === "ru" ? "🇬🇧" : "🇷🇺";

    const label = document.createElement("span");
    label.className = "lang-label";
    label.textContent = lang === "ru" ? "EN" : "RU";

    btn.appendChild(icon);
    btn.appendChild(label);

    btn.addEventListener("click", switchLanguage);

    const target = document.querySelector(".right-buttons");

    if (target) {
      target.insertBefore(btn, target.firstChild);
    }
  }

  // ---------------------------------
  // Init
  // ---------------------------------

  function init() {
    autoSelectLanguage();
    addSwitcher();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();