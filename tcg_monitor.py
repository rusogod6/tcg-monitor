#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
TCG Monitor -> Discord  (Pokémon TCG, One Piece TCG, Riftbound)

Detectează PRODUSE NOI și REVENIRI ÎN STOC pe magazinele din SITES și trimite
alertă pe Discord (cu @everyone) printr-un webhook.

Instalare:    pip install requests
Webhook:      export DISCORD_WEBHOOK_URL="https://discord.com/api/webhooks/..."
              (Windows PowerShell:  $env:DISCORD_WEBHOOK_URL="https://...")
Verificare:   python tcg_monitor.py --check          # testează fiecare site, fără Discord
              python tcg_monitor.py --test-discord   # trimite un mesaj de test (fără ping)
Rulare:       python tcg_monitor.py                  # rulează continuu (Ctrl+C oprește)
              python tcg_monitor.py --once           # un singur ciclu
              python tcg_monitor.py --debug pokemania  # diagnostic: arată HTML-ul brut al cardurilor unui site

La prima rulare, ce există deja pe fiecare site e salvat ca „baseline" (fără alerte).
Starea e în state.json; șterge fișierul ca să reiei de la zero.
"""
from __future__ import annotations

import argparse
import copy
import html as htmllib
import json
import os
import random
import re
import sys
import tempfile
import time
import unicodedata
from urllib.parse import parse_qsl, urlencode, urljoin, urlparse, urlunparse
from urllib.robotparser import RobotFileParser

import requests

# ───────────────────────────── CONFIG ─────────────────────────────
WEBHOOK_URL = os.environ.get("DISCORD_WEBHOOK_URL", "")
PING = os.environ.get("PING", "@everyone")            # "" ca să dezactivezi ping-ul
CYCLE_SECONDS = int(os.environ.get("CYCLE_SECONDS", "120"))
STATE_FILE = os.environ.get("STATE_FILE", "state.json")
RESPECT_ROBOTS = True        # sare peste paginile interzise de robots.txt
EXCLUDE_SINGLES = True       # ignoră cărți individuale (ex. "Pikachu ex 033/106")
MAX_DETAIL_FETCH_PER_SITE = 15   # câte pagini de produs se deschid per ciclu pentru detalii
MAX_RUNTIME = int(os.environ.get("MAX_RUNTIME", "0"))  # secunde; după ce trece, se sar verificările pe paginile de produs (0 = fără limită)
_DEADLINE = 0.0
DETAIL_BUDGET = int(os.environ.get("DETAIL_BUDGET", "12"))  # câte produse cu stoc necunoscut se re-verifică per ciclu/site
FLOOD_LIMIT = 40             # peste atâtea produse „noi" deodată pe un site = probabil defect, nu alertăm
ALERT_PREORDER = os.environ.get("ALERT_PREORDER", "1") != "0"   # "0" = alertă doar pentru „în stoc", nu și precomenzi
RESTOCK_COOLDOWN = 1800     # secunde minime între două alerte de restock pentru același produs
ERROR_NOTICE_AFTER = 10      # după câte eșecuri consecutive anunțăm pe Discord (fără ping)
WINDOW_MAX = 2500
USER_AGENT = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/126.0 Safari/537.36")

# Fiecare site: type "shopify" (JSON, foarte fiabil) sau "html" (extrage linkuri de produs din listări).
# html: lists = [{"url", "pages", "style", "game"}]; style: "gomag" (?p=n-1), "page" (?page=n), "p" (?p=n)
SITES = [
    {"key": "tcgarena", "name": "TCG Arena", "type": "shopify", "base": "https://tcgarena.ro",
     "lists": [("joc-de-carti-pokemon-tcg-romania", "Pokémon TCG"),
               ("cartonase-one-piece", "One Piece TCG"),
               ("cartonase-riftbound", "Riftbound")]},

    {"key": "redgoblin", "name": "Red Goblin", "type": "shopify", "base": "https://redgoblin.ro", "sealed_only": True,
     "lists": [("pokemon", "Pokémon TCG"), ("pokemon-1", "Pokémon TCG"),
               ("one-piece", "One Piece TCG"), ("riftbound", "Riftbound")]},

    {"key": "lexshop", "name": "LexShop", "type": "html", "base": "https://www.lexshop.ro", "assume_in_stock": True,
     "product_re": r"^/[a-z0-9\-]+/[a-z0-9\-%]+\.html$",
     "lists": [{"url": "https://www.lexshop.ro/pokemon-tcg?o=news", "pages": 6, "style": "gomag", "game": "Pokémon TCG"},
               {"url": "https://www.lexshop.ro/one-piece-card-game?o=news", "pages": 3, "style": "gomag", "game": "One Piece TCG"},
               {"url": "https://www.lexshop.ro/riftbound-league-of-legends-tcg?o=news", "pages": 2, "style": "gomag", "game": "Riftbound"}]},

    {"key": "ramcards", "name": "RamCards", "type": "html", "base": "https://www.ramcards.ro", "assume_in_stock": True,
     "product_re": r"^/[a-z0-9\-]+/[a-z0-9\-%]+\.html$",
     "lists": [{"url": "https://www.ramcards.ro/pokemon-tcg?o=news", "pages": 5, "style": "gomag", "game": "Pokémon TCG"},
               {"url": "https://www.ramcards.ro/one-piece-tcg?o=news", "pages": 3, "style": "gomag", "game": "One Piece TCG"},
               {"url": "https://www.ramcards.ro/riftbound-tcg?o=news", "pages": 2, "style": "gomag", "game": "Riftbound"}]},

    {"key": "krit", "name": "Krit.ro", "type": "html", "base": "https://krit.ro", "detail_budget": 25,
     "product_re": r"^/produs/[^/]+$",
     "lists": [{"url": "https://krit.ro/", "pages": 1, "style": "page"},
               {"url": "https://krit.ro/categorie/pokemon?sort=new", "pages": 8, "style": "page", "game": "Pokémon TCG"},
               {"url": "https://krit.ro/categorie/one-piece?sort=new", "pages": 5, "style": "page", "game": "One Piece TCG"},
               {"url": "https://krit.ro/categorie/riftbound-league-of-legends-tcg?sort=new", "pages": 4, "style": "page", "game": "Riftbound"},
               {"url": "https://krit.ro/categorie/trading-card-games?sort=new", "pages": 3, "style": "page"},
               {"url": "https://krit.ro/toate-produsele?sort=new&productsOnly=1", "pages": 3, "style": "page"},
               {"url": "https://krit.ro/toate-produsele?shelf=restock&sort=stocked&productsOnly=1", "pages": 2, "style": "page"}]},

    {"key": "pokemania", "name": "PokeMANIA", "type": "html", "base": "https://pokemania.ro", "assume_in_stock": True,
     "product_re": r"^/[a-z0-9\-%]+/[a-z0-9\-%]+$",
     "exclude_first_segments": ["catalog", "blog", "page", "pages", "cart", "login", "wishlist", "map", "contact",
                                "info", "account", "checkout", "search", "precomenzi"],
     "min_slug_hyphens": 3,
     "default_game": "Pokémon TCG",
     "lists": [{"url": "https://pokemania.ro/catalog/produse-recente", "pages": 3, "style": "page"},
               {"url": "https://pokemania.ro/precomenzi", "pages": 2, "style": "page"},
               {"url": "https://pokemania.ro/seturi-pokemon-tcg", "pages": 4, "style": "page"}]},
    # TODO: adaugă mai sus paginile One Piece și Riftbound de pe pokemania.ro (cu "game": "...") când ai URL-urile.

    # Același magazin ca pokemania.ro (engleză/USD) -> dezactivat ca să nu primești alerte duble.
    {"key": "thepokemania", "name": "ThePokeMANIA", "type": "html", "base": "https://thepokemania.com", "enabled": False,
     "product_re": r"^/[a-z0-9\-%]+/[a-z0-9\-%]+$",
     "exclude_first_segments": ["catalog", "blog", "page", "pages", "cart", "login", "wishlist", "map", "contact"],
     "default_game": "Pokémon TCG",
     "lists": [{"url": "https://thepokemania.com/catalog/new", "pages": 3, "style": "page"},
               {"url": "https://thepokemania.com/preorders", "pages": 2, "style": "page"},
               {"url": "https://thepokemania.com/pokemon-tcg-sets", "pages": 4, "style": "page"}]},

    {"key": "tcgshop", "name": "TCG-Shop", "type": "html", "base": "https://www.tcg-shop.ro", "assume_in_stock": True,
     "product_re": r"^/products/[^/]+$",
     "lists": [{"url": "https://www.tcg-shop.ro/category/pokemon", "pages": 5, "style": "page", "game": "Pokémon TCG"},
               {"url": "https://www.tcg-shop.ro/category/one-piece", "pages": 3, "style": "page", "game": "One Piece TCG"},
               {"url": "https://www.tcg-shop.ro/category/riftbound-league-of-legends-tcg", "pages": 2, "style": "page", "game": "Riftbound"}]},

    # Magento: legături de produs identificate prin clasa "product-item-link" (neverificat pe site live).
    {"key": "bookcity", "name": "BookCity", "type": "html", "base": "https://www.bookcity.ro", "enabled": False,  # robots.txt interzice listările
     "link_class": "product-item-link", "experimental": True,
     "lists": [{"url": "https://www.bookcity.ro/jocuri.html?manufacturer=71197&product_list_order=new", "pages": 3,
                "style": "p", "game": "Pokémon TCG"}]},

    {"key": "noriel", "name": "Noriel", "type": "html", "base": "https://noriel.ro", "enabled": False,  # 0 produse găsite la test
     "link_class": "product-item-link", "experimental": True,
     "lists": [{"url": "https://noriel.ro/jocuri-de-societate/f/b/pokemon", "pages": 3, "style": "p", "game": "Pokémon TCG"}]},

    # Dezactivate: vezi explicațiile din răspuns.
    {"key": "noxlegacy", "name": "NOX Legacy", "type": "html", "base": "https://noxlegacy.com", "enabled": False,
     "lists": []},   # produsele se încarcă prin JavaScript; e nevoie de endpointul API (vezi răspunsul)
    {"key": "tcgmania", "name": "TCGMania", "type": "html", "base": "https://tcgmania.ro", "enabled": False,
     "lists": []},   # robots.txt interzice accesul automat; platformă neverificată
]

# ───────────────────────────── FILTRE ─────────────────────────────
GAME_RE = {
    "Pokémon TCG": re.compile(r"pokemon"),
    "One Piece TCG": re.compile(r"one[\s\-]?piece"),
    "Riftbound": re.compile(r"riftbound"),
}
OTHER_GAMES_RE = re.compile(
    r"magic:? the gathering|\bmtg\b|yu-?gi-?oh|lorcana|flesh and blood|star wars|digimon|dragon ball|"
    r"warhammer|sorcery|duel masters|weiss|union arena|gundam|naruto|d&d|dungeons")
EXCLUDE_RE = re.compile(
    r"funko|plush|figurin|tcg binder|storage binder|\bsleeves?\b|toploader|playmat|graded|\bpsa\b|\bcgc\b|"
    r"\bbgs\b|\bsgc\b|graad|collect aura|protectie|magnetic|deck box|carcasa|deckbox|alcove|ultra pro|"
    r"dragon shield|gamegenic|pocket portfolio|\balbum\b|vestimentatie|decoratiuni|benzi desenate")
SINGLE_RE = re.compile(r"\b\d{1,3}\s?/\s?\d{2,3}\b|\bsingles?\b")
# Pentru magazinele cu mii de produse (singles amestecate): păstrăm doar produsele sigilate.
SEALED_RE = re.compile(
    r"booster|display|\bbox\b|elite trainer|\betb\b|\btin\b|blister|bundle|collection|\bdeck\b|pachet|\bpack|"
    r"\bset\b|\bcase\b|starter|checklane|theme|precomanda|pre-order|preorder|\bpin\b|surprise|mystery|premium|"
    r"ultra|gift|calendar|stack|sealed|trainer|battle|cutie|sigilat|\bcarton")

OUT_MARKS = ("stoc epuizat", "epuizat", "out of stock", "sold out", "indisponibil", "alerta stoc",
             "anunta-ma", "anunta ma", "notify me")
PRE_MARKS = ("precomanda", "pre-order", "preorder", "pre order")
IN_MARKS = ("adauga in cos", "add to cart", "in stoc", "in stock", "stoc furnizor")
ORDERABLE = ("in_stock", "preorder")


# ───────────────────────────── UTILITARE ─────────────────────────────
def norm(s: str) -> str:
    s = unicodedata.normalize("NFKD", s or "")
    s = "".join(c for c in s if not unicodedata.combining(c))
    return re.sub(r"\s+", " ", s.lower()).strip()


def strip_tags(s: str) -> str:
    s = re.sub(r"<script.*?</script>|<style.*?</style>", " ", s or "", flags=re.S | re.I)
    s = re.sub(r"<[^>]+>", " ", s)
    return re.sub(r"\s+", " ", htmllib.unescape(s)).strip()


def with_param(url: str, key: str, val) -> str:
    p = urlparse(url)
    q = dict(parse_qsl(p.query, keep_blank_values=True))
    q[key] = str(val)
    return urlunparse(p._replace(query=urlencode(q)))


STYLES = {
    "gomag": lambda u, n: u if n == 1 else with_param(u, "p", n - 1),
    "page": lambda u, n: u if n == 1 else with_param(u, "page", n),
    "p": lambda u, n: u if n == 1 else with_param(u, "p", n),
}

_warned: set = set()


def warn_once(msg: str):
    if msg not in _warned:
        _warned.add(msg)
        print(f"[avertisment] {msg}", flush=True)


def status_from_text(text: str) -> str:
    t = norm(strip_tags(text))
    if any(m in t for m in OUT_MARKS):
        return "out"
    if any(m in t for m in PRE_MARKS):
        return "preorder"
    if any(m in t for m in IN_MARKS):
        return "in_stock"
    return "unknown"


def status_from_schema(v: str):
    v = norm(v).replace(" ", "")
    if "outofstock" in v or "soldout" in v or "discontinued" in v:
        return "out"
    if "preorder" in v or "presale" in v or "backorder" in v:
        return "preorder"
    if "instock" in v or "limitedavailability" in v or "onlineonly" in v:
        return "in_stock"
    return None


def accept(text: str, url: str, default_game):
    t = norm(f"{text} {urlparse(url).path.replace('-', ' ')}")
    if EXCLUDE_RE.search(t):
        return None
    if EXCLUDE_SINGLES and SINGLE_RE.search(t):
        return None
    for game, rx in GAME_RE.items():
        if rx.search(t):
            return game
    if OTHER_GAMES_RE.search(t):
        return None
    return default_game


ATTR_RE = re.compile(r'(?:title|aria-label|alt|value|placeholder|data-[\w-]+)=["\']([^"\']*)["\']', re.I)
CLASS_OUT = ("out-of-stock", "outofstock", "stoc-epuizat", "sold-out", "soldout", "no-stock", "nostock")


def window_status(window: str, site: dict):
    """Stoc dintr-un card de listă: text + atribute (title/aria-label/value) + clase CSS."""
    text = strip_tags(window) + " " + " ".join(ATTR_RE.findall(window))
    st = status_from_text(text)
    if st == "unknown" and any(c in window.lower() for c in CLASS_OUT):
        st = "out"
    assumed = False
    if st == "unknown" and site.get("assume_in_stock"):
        st, assumed = "in_stock", True
    return st, assumed


PRICE_RE = re.compile(r"(\d{1,3}(?:\.\d{3})*,\d{2}|\d+[\.,]\d{2})\s*(?:RON|lei)", re.I)
NOISE_PREFIX = re.compile(r"^(?:\s*(?:stoc epuizat|out of stock|sold out|epuizat|nou|new|-?\d+\s?%)\s*)+", re.I)
TRAIL_PRICE = re.compile(r"\s*\d[\d\.\s]*[,\.]\d{2}\s*(?:lei|ron).*$", re.I)


def clean_title(t: str) -> str:
    t = NOISE_PREFIX.sub("", t.strip())
    t = TRAIL_PRICE.sub("", t)
    return t.strip(" -–|")


def slug_title(url: str) -> str:
    slug = urlparse(url).path.rstrip("/").split("/")[-1]
    slug = re.sub(r"\.html?$", "", slug)
    return slug.replace("-", " ").strip().title()


# ───────────────────────────── HTTP ─────────────────────────────
def make_session() -> requests.Session:
    s = requests.Session()
    s.headers.update({"User-Agent": USER_AGENT, "Accept-Language": "ro-RO,ro;q=0.9,en;q=0.7",
                      "Accept": "text/html,application/json;q=0.9,*/*;q=0.8"})
    return s


def http_get(session, url, **kw):
    last = None
    for attempt in range(3):
        try:
            r = session.get(url, timeout=25, **kw)
            if r.status_code in (429, 503):
                ra = r.headers.get("Retry-After", "")
                time.sleep(min(int(ra) if ra.isdigit() else 10 * (attempt + 1), 60))
                last = RuntimeError(f"HTTP {r.status_code} la {url}")
                continue
            return r
        except requests.RequestException as e:
            last = e
            time.sleep(2 * (attempt + 1))
    raise last


_robots: dict = {}


def robots_ok(session, url) -> bool:
    if not RESPECT_ROBOTS:
        return True
    p = urlparse(url)
    host = f"{p.scheme}://{p.netloc}"
    rp = _robots.get(host)
    if rp is None:
        rp = RobotFileParser()
        try:
            r = session.get(host + "/robots.txt", timeout=15)
            rp.parse(r.text.splitlines() if r.status_code == 200 else [])
        except requests.RequestException:
            rp.parse([])
        _robots[host] = rp
    return rp.can_fetch("*", url)


# ───────────────────────────── SCANARE ─────────────────────────────
A_RE = re.compile(r"<a\b([^>]*)>(.*?)</a>", re.I | re.S)
HREF_RE = re.compile(r'href=["\']([^"\']+)["\']', re.I)


def extract_products(html: str, page_url: str, site: dict) -> list:
    host = urlparse(site["base"]).netloc.replace("www.", "")
    rx = site.get("product_re")
    skip_seg = set(site.get("exclude_first_segments", []))
    link_class = site.get("link_class")
    order, first, texts = [], {}, {}
    for m in A_RE.finditer(html):
        attrs, inner = m.group(1), m.group(2)
        hm = HREF_RE.search(attrs)
        if not hm:
            continue
        if link_class and link_class not in attrs:
            continue
        u = urljoin(page_url, htmllib.unescape(hm.group(1))).split("#")[0]
        pu = urlparse(u)
        if pu.netloc.replace("www.", "") != host:
            continue
        path = pu.path
        if rx and not re.search(rx, path):
            continue
        segs = [x for x in path.split("/") if x]
        if not segs or segs[0] in skip_seg or segs[0] in ("en",):
            continue
        if site.get("min_slug_hyphens") and segs[-1].count("-") < site["min_slug_hyphens"]:
            continue      # slug scurt = pagină de categorie, nu produs
        key = urlunparse((pu.scheme, pu.netloc, path, "", "", ""))
        if key not in first:
            first[key] = m.start()
            order.append(key)
        texts.setdefault(key, []).append(strip_tags(inner))
    items = []
    for i, u in enumerate(order):
        end = first[order[i + 1]] if i + 1 < len(order) else len(html)
        window = html[first[u]:min(end, first[u] + WINDOW_MAX)]
        cands = [clean_title(t) for t in texts[u]]
        cands = [c for c in cands if len(c) >= 8 and not PRICE_RE.fullmatch(c)]
        from_slug = not cands
        title = max(cands, key=len) if cands else slug_title(u)
        pm = PRICE_RE.search(strip_tags(window))
        price = f"{pm.group(1)} RON" if pm else None
        status, assumed = window_status(window, site)
        items.append({"url": u, "title": title, "title_from_slug": from_slug, "status": status,
                      "assumed": assumed, "price": price, "image": None, "_win": window[:900]})
    return items


def scan_html(session, site) -> dict:
    items = {}
    lists = list(site["lists"])
    if site.get("discover"):      # găsește singur categoriile (ex. One Piece, Riftbound) pe prima pagină
        host = urlparse(site["base"]).netloc.replace("www.", "")
        found = {}
        try:
            hr = http_get(session, site["base"] + "/")
            for hm in HREF_RE.finditer(hr.text):
                pu = urlparse(urljoin(site["base"] + "/", htmllib.unescape(hm.group(1))))
                segs = [x for x in pu.path.split("/") if x]
                if pu.netloc.replace("www.", "") != host or len(segs) != 1:
                    continue
                for rx, game in site["discover"]:
                    if re.search(rx, segs[0]):
                        found[pu.path] = game
        except requests.RequestException as e:
            warn_once(f"{site['name']}: nu pot citi pagina principală ({e})")
        if not found:
            warn_once(f"{site['name']}: nu am găsit automat categoriile {[g for _, g in site['discover']]}; "
                      f"trimite-mi URL-urile lor")
        for path, game in list(found.items())[:4]:
            lists.append({"url": site["base"] + path, "pages": 3, "style": "page", "game": game})
    for lst in lists:
        seen = set()
        for n in range(1, lst.get("pages", 1) + 1):
            url = STYLES[lst.get("style", "page")](lst["url"], n)
            if not robots_ok(session, url):
                warn_once(f"{site['name']}: robots.txt interzice {url}, sar peste")
                break
            r = http_get(session, url)
            if r.status_code == 404:
                if n == 1:      # 404 pe paginile următoare = sfârșitul listei (normal)
                    warn_once(f"{site['name']}: 404 la {url} (verifică URL-ul)")
                break
            r.raise_for_status()
            found = [f for f in extract_products(r.text, url, site) if f["url"] not in seen]
            if not found:
                break
            for f in found:
                seen.add(f["url"])
                game = accept(f["title"], f["url"], lst.get("game") or site.get("default_game"))
                if game:
                    f["game"] = game
                    items.setdefault(f["url"], f)
            time.sleep(random.uniform(0.8, 2.0))
    return items


def scan_shopify(session, site) -> dict:
    items = {}
    for handle, game in site["lists"]:
        for page in range(1, 9):
            url = f"{site['base']}/collections/{handle}/products.json?limit=250&page={page}"
            if not robots_ok(session, url):
                warn_once(f"{site['name']}: robots.txt interzice {url}, sar peste")
                break
            r = http_get(session, url)
            if r.status_code == 404:
                warn_once(f"{site['name']}: colecția '{handle}' nu există (404)")
                break
            r.raise_for_status()
            prods = r.json().get("products", [])
            if not prods:
                break
            for p in prods:
                tags = p.get("tags") or []
                tags = " ".join(tags) if isinstance(tags, list) else str(tags)
                title = p.get("title", "")
                purl = f"{site['base']}/products/{p.get('handle', '')}"
                g = accept(f"{title} {p.get('product_type', '')} {tags}", purl, game)
                if not g:
                    continue
                if site.get("sealed_only") and not SEALED_RE.search(norm(f"{title} {p.get('product_type', '')}")):
                    continue
                variants = p.get("variants") or []
                avail = any(v.get("available") for v in variants)
                status = "out"
                if avail:
                    status = "preorder" if any(m in norm(title) for m in PRE_MARKS) else "in_stock"
                prices = []
                for v in variants:
                    try:
                        prices.append(float(v.get("price")))
                    except (TypeError, ValueError):
                        pass
                img = (p.get("images") or [{}])[0].get("src")
                items.setdefault(purl, {"url": purl, "title": title, "title_from_slug": False, "status": status,
                                        "price": f"{min(prices):.2f} RON" if prices else None,
                                        "image": img, "game": g, "ptype": p.get("product_type", "")})
            if len(prods) < 250:
                break
            time.sleep(random.uniform(0.8, 1.5))
    return items


def scan(session, site) -> dict:
    return scan_shopify(session, site) if site["type"] == "shopify" else scan_html(session, site)


def meta(html: str, key: str):
    for m in re.finditer(r"<meta\b[^>]*>", html, re.I):
        tag = m.group(0)
        if re.search(r'(?:property|name|itemprop)=["\']%s["\']' % re.escape(key), tag, re.I):
            c = re.search(r'content=["\']([^"\']*)["\']', tag, re.I)
            if c:
                return htmllib.unescape(c.group(1)).strip()
    return None


def fetch_details(session, url: str) -> dict:
    r = http_get(session, url)
    r.raise_for_status()
    h = r.text
    d = {"title": meta(h, "og:title"), "image": meta(h, "og:image"), "price": None, "status": None}
    m = re.search(r'"availability"\s*:\s*"([^"]+)"', h)
    if m:
        d["status"] = status_from_schema(m.group(1))
    if d["status"] is None:
        a = meta(h, "product:availability") or meta(h, "og:availability")
        if a:
            d["status"] = status_from_schema(a)
    price = meta(h, "product:price:amount") or meta(h, "og:price:amount")
    cur = meta(h, "product:price:currency") or meta(h, "og:price:currency")
    if not price:
        pm = re.search(r'"price"\s*:\s*"?([\d.,]+)"?', h)
        cm = re.search(r'"priceCurrency"\s*:\s*"([A-Za-z]{3})"', h)
        price, cur = (pm.group(1) if pm else None), (cm.group(1) if cm else cur)
    if price:
        price = str(price).strip().rstrip(",.")
        d["price"] = f"{price} {cur or ''}".strip()
    if d["title"]:
        d["title"] = re.split(r"\s+[\|–—]\s+", d["title"])[0].strip()
    return d


# ───────────────────────────── DISCORD ─────────────────────────────
STATUS_LABEL = {"in_stock": "✅ În stoc", "preorder": "🕒 Precomandă", "out": "❌ Stoc epuizat",
                "unknown": "❔ Stoc necunoscut"}


def discord_send(content: str, embeds: list, ping: bool):
    payload = {"content": content[:2000], "embeds": embeds[:10],
               "allowed_mentions": {"parse": ["everyone"] if ping else []}}
    for _ in range(4):
        r = requests.post(WEBHOOK_URL, json=payload, timeout=20)
        if r.status_code == 429:
            try:
                wait = float(r.json().get("retry_after", 2))
            except Exception:
                wait = 2.0
            time.sleep(wait + 0.5)
            continue
        r.raise_for_status()
        return
    raise RuntimeError("Discord: prea multe cereri (429)")


def build_embed(ev: dict) -> dict:
    it = ev["item"]
    desc = " • ".join(x for x in [it.get("game"), it.get("price"), STATUS_LABEL.get(it["status"])] if x)
    desc += f"\n🛒 [Cumpără acum]({it['url']})"
    e = {"title": it["title"][:250], "url": it["url"], "description": desc,
         "color": 0x3498DB if ev["type"] == "new" else 0x2ECC71, "footer": {"text": ev["site"]}}
    if it.get("image"):
        e["thumbnail"] = {"url": it["image"]}
    return e


def notify_events(site_name: str, events: list):
    labels = {"new": ("🆕", "produs nou", "produse noi"), "restock": ("🟢", "înapoi în stoc", "înapoi în stoc")}
    for typ in ("new", "restock"):
        evs = [e for e in events if e["type"] == typ]
        for i in range(0, len(evs), 10):
            chunk = evs[i:i + 10]
            emoji, one, many = labels[typ]
            head = f"{emoji} {len(chunk)} {one if len(chunk) == 1 else many} pe {site_name}"
            discord_send(f"{PING} {head}".strip(), [build_embed(e) for e in chunk], ping=bool(PING))
            time.sleep(1.0)


def notice(text: str):
    try:
        discord_send(text, [], ping=False)
    except Exception as e:  # nu blocăm monitorul din cauza unui mesaj informativ
        print(f"[eroare notificare] {e}", flush=True)


# ───────────────────────────── LOGICA DE DIFF ─────────────────────────────
def rec(it: dict, now: float, alerted: bool = False, old: dict | None = None) -> dict:
    status = it["status"]
    if (status == "unknown" or it.get("assumed")) and old:      # un stoc doar „presupus" nu suprascrie unul verificat
        status = old.get("status", status)
    r = {"title": it["title"], "url": it["url"], "status": status, "price": it.get("price"),
         "game": it.get("game"), "first_seen": (old or {}).get("first_seen", now),
         "alerted_at": (old or {}).get("alerted_at", 0), "checked_at": (old or {}).get("checked_at", 0)}
    if alerted:
        r["alerted_at"] = now
    return r


def resolve_by_detail(session, site: dict, items: dict, prev: dict, now: float) -> list:
    """Pentru produsele al căror stoc nu se vede în listare, verifică pagina produsului (cu buget per ciclu).
    Întâi cele epuizate/necunoscute (ca să prindă revenirile), apoi cele mai demult verificate."""
    budget = site.get("detail_budget", DETAIL_BUDGET)
    if budget <= 0:
        return []
    cand = [u for u, it in items.items() if (it["status"] == "unknown" or it.get("assumed")) and u in prev]

    def prio(u):      # cele neverificate încă primele, apoi cele mai demult verificate (epuizatele cu avans)
        o = prev[u]
        c = o.get("checked_at", 0)
        return -1e12 if c == 0 else c - (900 if o["status"] == "out" else 0)

    cand.sort(key=prio)
    evs = []
    for u in cand[:budget]:
        if _DEADLINE and time.time() > _DEADLINE:
            print(f"[detalii] {site['name']}: timpul alocat s-a terminat, restul verificărilor la ciclul următor", flush=True)
            break
        old = prev[u]
        old_status = old["status"]
        old["checked_at"] = now
        try:
            d = fetch_details(session, u)
        except Exception as e:
            print(f"[detalii] {u}: {e}", flush=True)
            continue
        st = d.get("status")
        if st:
            it = items[u]
            if old_status == "out" and st in ORDERABLE and now - old.get("alerted_at", 0) >= RESTOCK_COOLDOWN:
                if d.get("image"):
                    it["image"] = d["image"]
                if d.get("price"):
                    it["price"] = d["price"]
                evs.append({"type": "restock", "site": site["name"], "item": it})
            it["status"], it["assumed"] = st, False
            old["status"] = st
        time.sleep(random.uniform(0.5, 1.2))
    return evs


def process_site(session, site: dict, items: dict, s: dict):
    """Modifică s (starea site-ului) și întoarce (evenimente, baseline_count|None, mesaj_flood|None)."""
    prev, now = s["items"], time.time()
    if s["init"] and not items and prev:
        raise RuntimeError("0 produse găsite (structura paginii s-a schimbat sau accesul e blocat?)")
    if not s["init"]:
        for url, it in items.items():
            prev[url] = rec(it, now)
        s["init"] = True
        return [], f"{sum(1 for i in items.values() if i['status'] in ('in_stock', 'preorder'))} disponibile din {len(items)}", None

    events = []
    for url, it in items.items():
        old = prev.get(url)
        if old is None:
            events.append({"type": "new", "site": site["name"], "item": it})
        elif (old["status"] == "out" and it["status"] in ORDERABLE and not it.get("assumed")
              and now - old.get("alerted_at", 0) >= RESTOCK_COOLDOWN):
            events.append({"type": "restock", "site": site["name"], "item": it})

    n_new = sum(1 for e in events if e["type"] == "new")
    if n_new > FLOOD_LIMIT:
        for url, it in items.items():
            prev[url] = rec(it, now, old=prev.get(url))
        return [], None, (f"⚠️ {site['name']}: au apărut {n_new} produse „noi” deodată. Probabil s-a schimbat "
                          f"structura site-ului; le-am marcat ca văzute, fără alerte individuale.")

    final, fetched = [], 0
    for ev in events:
        it = ev["item"]
        if site["type"] != "shopify" and fetched < MAX_DETAIL_FETCH_PER_SITE:
            fetched += 1
            try:
                d = fetch_details(session, it["url"])
            except Exception as e:
                print(f"[detalii] {it['url']}: {e}", flush=True)
                d = None
            if d:
                if d.get("status") and ev["type"] == "restock" and d["status"] not in ORDERABLE:
                    it["status"] = d["status"]        # fals pozitiv din listare: nu alertăm
                    continue
                if d.get("status"):
                    it["status"] = d["status"]
                if d.get("image"):
                    it["image"] = d["image"]
                if d.get("price"):
                    it["price"] = d["price"]
                if d.get("title") and (it.get("title_from_slug") or len(it["title"]) < 10):
                    it["title"] = d["title"]
                    if not accept(it["title"], it["url"], it.get("game")):
                        prev[it["url"]] = rec(it, now)  # reevaluat după titlul real: exclus
                        continue
        final.append(ev)

    if site["type"] != "shopify":
        final.extend(resolve_by_detail(session, site, items, prev, now))
    ok_status = ("in_stock", "preorder") if ALERT_PREORDER else ("in_stock",)
    final = [e for e in final if e["item"]["status"] in ok_status or e["item"]["status"] == "unknown"]  # doar disponibile
    sent = {e["item"]["url"] for e in final}
    for url, it in items.items():
        prev[url] = rec(it, now, alerted=url in sent, old=prev.get(url))
    return final, None, None


def load_state() -> dict:
    try:
        with open(STATE_FILE, encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, json.JSONDecodeError):
        return {"sites": {}}


def save_state(state: dict):
    fd, tmp = tempfile.mkstemp(dir=os.path.dirname(os.path.abspath(STATE_FILE)), suffix=".tmp")
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False)
    os.replace(tmp, STATE_FILE)


_failures: dict = {}
_error_notified: set = set()


def run_cycle(session, sites: list, state: dict):
    global _DEADLINE
    _DEADLINE = time.time() + MAX_RUNTIME if MAX_RUNTIME else 0.0
    baselined = []
    for site in sites:
        key = site["key"]
        s = state["sites"].setdefault(key, {"init": False, "items": {}})
        backup = copy.deepcopy(s)
        try:
            items = scan(session, site)
            events, base, flood = process_site(session, site, items, s)
            if flood:
                notice(flood)
            if events:
                notify_events(site["name"], events)
                print(f"[{time.strftime('%H:%M:%S')}] {site['name']}: {len(events)} alerte trimise", flush=True)
            if base is not None:
                baselined.append(f"{site['name']}: {base}")
                if base == 0 and site.get("experimental"):
                    warn_once(f"{site['name']}: 0 produse găsite (site experimental, ajustează selectorii)")
            _failures[key] = 0
            _error_notified.discard(key)
            state["sites"][key] = s
            save_state(state)
        except Exception as e:
            state["sites"][key] = backup       # alerta neprocesată va fi redetectată la ciclul următor
            _failures[key] = _failures.get(key, 0) + 1
            print(f"[eroare] {site['name']}: {e}", flush=True)
            if _failures[key] >= ERROR_NOTICE_AFTER and key not in _error_notified:
                _error_notified.add(key)
                notice(f"⚠️ {site['name']}: {_failures[key]} erori la rând ({e}). Verifică monitorul.")
        time.sleep(random.uniform(1, 3))
    if baselined:
        notice("📋 Baseline salvat (fără alerte): " + " | ".join(baselined))


# ───────────────────────────── CLI ─────────────────────────────
def check(session, sites):
    for site in sites:
        print(f"\n=== {site['name']} ({site['type']}) ===")
        try:
            items = scan(session, site)
        except Exception as e:
            print(f"  EROARE: {e}")
            continue
        by = {}
        for it in items.values():
            by.setdefault((it["game"], it["status"]), 0)
            by[(it["game"], it["status"])] += 1
        print(f"  produse acceptate: {len(items)}")
        for (g, st), n in sorted(by.items(), key=lambda x: str(x)):
            print(f"    {g:14} {st:9} {n}")
        for it in list(items.values())[:3]:
            print(f"  ex: [{it['status']}] {it['title'][:70]}  {it.get('price') or ''}\n      {it['url']}")
        if site["type"] == "shopify" and items:
            from collections import Counter
            types = Counter((it.get("ptype") or "(gol)") for it in items.values()).most_common(10)
            print("  tipuri de produs: " + ", ".join(f"{t} ({n})" for t, n in types))
        if not items:
            print("  ATENȚIE: 0 produse; selectorii/URL-urile trebuie ajustate pentru acest site.")
        if site["type"] == "html" and items:
            first = next(iter(items.values()))
            try:
                d = fetch_details(session, first["url"])
                print(f"  pagină produs: status={d['status']} preț={d['price']} "
                      f"imagine={'da' if d['image'] else 'nu'} titlu={'da' if d['title'] else 'nu'}")
            except Exception as e:
                print(f"  pagină produs: EROARE {e}")
        if site["type"] == "html":
            unk = sum(1 for it in items.values() if it["status"] == "unknown")
            if items and unk / len(items) > 0.5:
                print(f"  ATENȚIE: {unk}/{len(items)} cu stoc „unknown”; textele de stoc din listare nu sunt recunoscute.")


def debug(session, key: str):
    """Arată HTML-ul brut al primelor carduri dintr-un site (pentru a ajusta detectarea stocului)."""
    site = next((s for s in SITES if s["key"] == key), None)
    if not site or site["type"] != "html":
        print("Folosește: --debug <cheie>; site-uri html: " + ", ".join(s["key"] for s in SITES if s["type"] == "html"))
        return
    for lst in site["lists"][:2]:
        url = lst["url"]
        print(f"\n--- {url}")
        r = http_get(session, url)
        print(f"HTTP {r.status_code}, {len(r.text)} caractere")
        items = extract_products(r.text, url, site)
        print(f"{len(items)} linkuri de produs găsite")
        pick = [i for i in items if i["status"] == "unknown" or i.get("assumed")][:2] + \
               [i for i in items if i["status"] != "unknown" and not i.get("assumed")][:1]
        for it in pick:
            w = re.sub(r"\s+", " ", it["_win"])
            print(f"\n[{it['status']}{' (presupus)' if it.get('assumed') else ''}] {it['title'][:80]}\n{it['url']}\n{w}")


def selftest() -> int:
    """Teste offline pe HTML sintetic (fără rețea, fără Discord)."""
    global http_get, robots_ok, discord_send, fetch_details, notice
    mp_site = {"key": "t", "name": "T", "type": "html", "base": "https://pokemania.ro",
               "product_re": r"^/[a-z0-9\-%]+/[a-z0-9\-%]+$",
               "exclude_first_segments": ["catalog", "blog"], "default_game": "Pokémon TCG",
               "lists": [{"url": "https://pokemania.ro/catalog/produse-recente", "pages": 2, "style": "page"}]}
    base_html = """
    <a href="/catalog/produse-recente">Produse noi</a> <a href="/blog/x/y">blog</a>
    <div><a href="/prismatic-evolutions/set-pokemon-tcg-prismatic-evolutions-etb"><img src="x"></a>
    <a href="https://pokemania.ro/prismatic-evolutions/set-pokemon-tcg-prismatic-evolutions-etb">NOU 16% Set Pokémon TCG Prismatic Evolutions Elite Trainer Box</a>
    <span>999,90 RON 1.199,90 RON</span><a href="/prismatic-evolutions/set-pokemon-tcg-prismatic-evolutions-etb">Adauga in cos</a></div>
    <div><a href="/figurine-funko-pop/figurina-funko-pop-pokemon-mewtwo-581">stoc epuizat 23% Figurina Funko POP! Pokémon - Mewtwo</a></div>
    <div><a href="/storm-emeralda/pokemon-tcg-storm-emeralda-booster-box">stoc epuizat Pokémon TCG: MEGA - Storm Emeralda Booster Box</a> 1.199,90 RON</div>
    <div><a href="/psa-graded/pikachu-ex-033-106-psa-10">Pikachu ex #033/106 PSA 10</a></div>
    """
    pages = {"html": base_html}
    sent, ok = [], []

    class Resp:
        def __init__(self, text="", status=200, js=None):
            self.text, self.status_code, self._js = text, status, js

        def json(self):
            return self._js

        def raise_for_status(self):
            if self.status_code >= 400:
                raise RuntimeError(self.status_code)

    def fake_get(session, url, **kw):
        if "collections/" in url and url.endswith("page=1"):
            return Resp(js=pages["shopify"])
        if "collections/" in url:
            return Resp(js={"products": []})
        if "page=2" in url:
            return Resp("")
        return Resp(pages["html"])

    http_get, robots_ok = fake_get, (lambda s, u: True)
    discord_send = lambda content, embeds, ping: sent.append((content, [e["title"] for e in embeds], ping))
    fetch_details = lambda s, u: {"title": None, "image": "https://img/x.jpg", "price": None,
                                  "status": pages.get("detail_status")}
    notice = lambda t: sent.append(("NOTICE " + t, [], False))

    def check_(cond, msg):
        ok.append(bool(cond))
        print(("OK   " if cond else "FAIL ") + msg)

    items = scan_html(None, mp_site)
    check_(len(items) == 2, f"filtrează funko/graded/blog -> 2 produse (găsit {len(items)})")
    st = {i["title"][:20]: i["status"] for i in items.values()}
    check_(list(st.values()) == ["in_stock", "out"], f"statusuri din listare corecte: {st}")
    check_(items["https://pokemania.ro/prismatic-evolutions/set-pokemon-tcg-prismatic-evolutions-etb"]["price"]
           == "999,90 RON", "preț extras")

    state = {"sites": {}}
    session = None
    run_cycle(session, [mp_site], state)
    check_(all("NOTICE" in c[0] and "Baseline" in c[0] for c in sent) and len(sent) == 1, "ciclul 1 = baseline, fără alerte")
    sent.clear()
    pages["html"] = base_html + '<div><a href="/pitch-black/pachet-pokemon-pitch-black-booster">Pachet Pokémon Pitch Black Booster</a> 29,90 RON <a href="/pitch-black/pachet-pokemon-pitch-black-booster">Adauga in cos</a></div>'
    run_cycle(session, [mp_site], state)
    check_(len(sent) == 1 and sent[0][2] and sent[0][0].startswith("@everyone 🆕") and "Pitch Black" in sent[0][1][0],
           f"produs nou -> alertă cu @everyone: {sent}")
    sent.clear()
    pages["html"] = pages["html"].replace(
        "stoc epuizat Pokémon TCG: MEGA - Storm Emeralda Booster Box", "Pokémon TCG: MEGA - Storm Emeralda Booster Box Adauga in cos")
    pages["detail_status"] = "out"
    run_cycle(session, [mp_site], state)
    check_(not sent, "restock infirmat de pagina produsului -> fără alertă (fals pozitiv suprimat)")
    pages["detail_status"] = None
    state["sites"]["t"]["items"]["https://pokemania.ro/storm-emeralda/pokemon-tcg-storm-emeralda-booster-box"]["status"] = "out"
    pages["detail_status"] = "in_stock"
    run_cycle(session, [mp_site], state)
    check_(len(sent) == 1 and "🟢" in sent[0][0], f"restock confirmat -> alertă: {sent}")
    sent.clear()
    run_cycle(session, [mp_site], state)
    check_(not sent, "fără repetare a alertei la ciclul următor")

    # statusuri din atribute + rezolvare prin pagina produsului când listarea nu arată stocul
    check_(window_status('<a title="Adauga in cos" href="/x"></a>', {})[0] == "in_stock", "status din atributul title")
    check_(window_status('<a class="btn out-of-stock" href="/x">Cumpara</a>', {})[0] == "out", "status din clasa out-of-stock")
    rs_site = dict(mp_site, key="rs", name="RS")
    rs_site["lists"] = [{"url": "https://pokemania.ro/catalog/rs", "pages": 1, "style": "page"}]
    pages["html"] = '<div><a href="/cat/pokemon-tcg-box-one-edition">Pokemon TCG Box One Edition</a> 10,00 RON</div>'
    pages["detail_status"] = None
    st3 = {"sites": {}}
    run_cycle(session, [rs_site], st3)   # baseline
    sent.clear()
    st3["sites"]["rs"]["items"]["https://pokemania.ro/cat/pokemon-tcg-box-one-edition"]["status"] = "out"
    pages["detail_status"] = "in_stock"
    run_cycle(session, [rs_site], st3)
    check_(len(sent) == 1 and "🟢" in sent[0][0], f"restock găsit prin pagina produsului (listare fără marcaje): {sent}")
    sent.clear()
    run_cycle(session, [rs_site], st3)
    check_(not sent, "fără repetare după rezolvare")

    # site cu stoc „presupus": un produs verificat ca epuizat rămâne epuizat, iar revenirea e prinsă prin pagina produsului
    rs2 = dict(rs_site, key="rs2", name="RS2", assume_in_stock=True)
    pages["detail_status"] = None
    st4 = {"sites": {}}
    run_cycle(session, [rs2], st4)
    sent.clear()
    k = "https://pokemania.ro/cat/pokemon-tcg-box-one-edition"
    st4["sites"]["rs2"]["items"][k]["status"] = "out"
    pages["detail_status"] = "out"
    run_cycle(session, [rs2], st4)
    run_cycle(session, [rs2], st4)
    check_(not sent and st4["sites"]["rs2"]["items"][k]["status"] == "out", f"presupus în stoc, dar verificat epuizat: rămâne epuizat, fără alerte {sent}")
    pages["detail_status"] = "in_stock"
    run_cycle(session, [rs2], st4)
    check_(len(sent) == 1 and "🟢" in sent[0][0], f"revenire confirmată pe pagina produsului -> alertă: {sent}")

    # produs nou epuizat = fără alertă; produs nou disponibil = alertă
    rs3 = dict(mp_site, key="rs3", name="RS3")
    rs3["lists"] = [{"url": "https://pokemania.ro/catalog/rs3", "pages": 1, "style": "page"}]
    a1 = '<div><a href="/cat/pokemon-tcg-box-alpha-edition">stoc epuizat Pokemon TCG Box Alpha Edition</a></div>'
    pages["html"], pages["detail_status"] = a1, None
    st5 = {"sites": {}}
    run_cycle(session, [rs3], st5)
    sent.clear()
    a2 = a1 + '<div><a href="/cat/pokemon-tcg-box-beta-edition">stoc epuizat Pokemon TCG Box Beta Edition</a></div>'
    pages["html"] = a2
    run_cycle(session, [rs3], st5)
    check_(not sent, f"produs nou epuizat -> fără alertă: {sent}")
    pages["html"] = a2 + '<div><a href="/cat/pokemon-tcg-box-gamma-edition">Pokemon TCG Box Gamma Edition</a> <a href="/cat/pokemon-tcg-box-gamma-edition">Adauga in cos</a></div>'
    run_cycle(session, [rs3], st5)
    check_(len(sent) == 1 and "Gamma" in sent[0][1][0], f"produs nou disponibil -> alertă: {sent}")
    check_("Cumpără acum" in build_embed({"type": "new", "site": "x", "item": {
        "title": "t", "url": "https://u", "status": "in_stock", "game": "g", "price": None}})["description"],
        "embed-ul conține linkul")

    # Shopify
    sh_site = {"key": "s", "name": "S", "type": "shopify", "base": "https://shop.ro",
               "lists": [("one-piece", "One Piece TCG")]}
    pages["shopify"] = {"products": [
        {"id": 1, "title": "One Piece OP10 Booster Box", "handle": "op10-box", "tags": ["sealed"], "product_type": "Box",
         "variants": [{"available": False, "price": "599.00"}], "images": [{"src": "https://i/1.jpg"}]},
        {"id": 2, "title": "Luffy Single OP10-001 12/100", "handle": "luffy", "tags": "single", "product_type": "Single",
         "variants": [{"available": True, "price": "5.00"}], "images": []}]}
    state2 = {"sites": {}}
    sent.clear()
    run_cycle(session, [sh_site], state2)
    check_(len(state2["sites"]["s"]["items"]) == 1, "shopify: single exclus, box păstrat")
    sent.clear()
    pages["shopify"]["products"][0]["variants"][0]["available"] = True
    run_cycle(session, [sh_site], state2)
    check_(len(sent) == 1 and sent[0][2], f"shopify: revenire în stoc -> alertă: {sent}")

    print(f"\n{sum(ok)}/{len(ok)} teste trecute")
    return 0 if all(ok) else 1


def main() -> int:
    ap = argparse.ArgumentParser(description="Monitor TCG -> Discord")
    ap.add_argument("--check", action="store_true", help="testează site-urile (fără Discord/stare)")
    ap.add_argument("--test-discord", action="store_true", help="trimite un mesaj de test (fără ping)")
    ap.add_argument("--once", action="store_true", help="un singur ciclu")
    ap.add_argument("--selftest", action="store_true", help="teste offline")
    ap.add_argument("--debug", metavar="CHEIE", help="arată HTML-ul brut al cardurilor unui site (ex: pokemania)")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    sites = [s for s in SITES if s.get("enabled", True)]
    session = make_session()
    if args.debug:
        debug(session, args.debug)
        return 0
    if args.check:
        check(session, sites)
        return 0
    if not WEBHOOK_URL:
        print("Setează variabila DISCORD_WEBHOOK_URL (vezi începutul fișierului).")
        return 2
    if args.test_discord:
        discord_send("✅ Monitorul TCG e conectat la Discord.", [], ping=False)
        print("Mesaj de test trimis.")
        return 0
    state = load_state()
    print(f"Monitorizez {len(sites)} site-uri, ciclu ~{CYCLE_SECONDS}s. Ctrl+C oprește.", flush=True)
    try:
        while True:
            run_cycle(session, sites, state)
            if args.once:
                break
            time.sleep(CYCLE_SECONDS + random.uniform(0, 20))
    except KeyboardInterrupt:
        print("Oprit.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
