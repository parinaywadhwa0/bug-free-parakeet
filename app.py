"""
Indian Company Contact Scraper
===============================
Scrapes official websites of Indian companies for contact info:
emails, phone numbers, about text, address, GSTIN, CIN.

Usage:
    # As a Python function
    from app import scrape_companies_sync
    import json
    data = json.load(open("companyDataM.json"))
    results = scrape_companies_sync(data, start=1, end=50)

    # As CLI
    python app.py --input companyDataM.json --output results.json --start 1 --end 50
"""

import asyncio
import json
import logging
import os
import random
import re
import sys
import time
from pathlib import Path
from typing import Optional
from urllib.parse import urljoin, urlparse

import cloudscraper
import httpx
import phonenumbers
import trafilatura
from bs4 import BeautifulSoup
from duckduckgo_search import DDGS
from fake_useragent import UserAgent
from thefuzz import fuzz

# ─── Configuration ───────────────────────────────────────────────────────────

MAX_CONCURRENT_HTTP = 50
MAX_CONCURRENT_BROWSERS = 10
SEARCH_DELAY_SECONDS = 2
REQUEST_DELAY_RANGE = (1, 3)
INTERNAL_BATCH_SIZE = 50
MAX_RETRIES = 2
DEFAULT_REGION = "IN"
URL_CACHE_FILE = "url_cache.json"
RESULTS_CACHE_FILE = "results_cache.json"

# Names that are too generic or invalid to scrape
JUNK_NAME_PATTERNS = [
    "n/a", "none", "freelance", "freelancer", "individual projects",
    "pvt ltd company", "pet store", "call center", "not applicable",
    "test", "demo", "sample", "unknown", "na", "nil", "null",
]

# Domains to exclude from "official website" results
DIRECTORY_BLOCKLIST = [
    "linkedin.com", "facebook.com", "wikipedia.org", "youtube.com",
    "glassdoor.com", "glassdoor.co.in", "ambitionbox.com", "naukri.com",
    "twitter.com", "x.com", "instagram.com", "indeed.com", "crunchbase.com",
    "zaubacorp.com", "tofler.in", "fundoodata.com",
]

# Indian directory sites (used as fallback source)
INDIAN_DIRECTORIES = ["justdial.com", "indiamart.com"]

# Preferred TLDs for Indian companies
PREFERRED_TLDS = [".in", ".co.in", ".gov.in", ".nic.in", ".org.in", ".ac.in"]

# Common about/contact page paths
ABOUT_PATHS = [
    "/about", "/about-us", "/about-us/", "/aboutus",
    "/company", "/who-we-are", "/our-company", "/our-story",
    "/about-company", "/about-company.html", "/about.html",
]
CONTACT_PATHS = [
    "/contact", "/contact-us", "/contact-us/", "/contactus",
    "/reach-us", "/get-in-touch", "/contact.html",
]

# ─── Logging ─────────────────────────────────────────────────────────────────

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S",
)
logger = logging.getLogger("scraper")

# ─── Cache Management ────────────────────────────────────────────────────────

def load_cache(filepath: str) -> dict:
    """Load a JSON cache file. Returns empty dict if not found."""
    p = Path(filepath)
    if p.exists():
        try:
            return json.loads(p.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            return {}
    return {}


def save_cache(filepath: str, data: dict):
    """Persist cache dict to a JSON file."""
    Path(filepath).write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")


# ─── Input Cleaning ──────────────────────────────────────────────────────────

def clean_company_name(fname: str) -> str:
    """Strip whitespace, normalize spacing."""
    name = fname.strip()
    name = re.sub(r"\s+", " ", name)  # collapse multiple spaces
    return name


def is_junk_name(name: str) -> Optional[str]:
    """
    Check if a company name is invalid/unscrappable.
    Returns the reason string if junk, or None if valid.
    """
    lower = name.lower().strip()

    if len(lower) < 3:
        return "name_too_short"

    if lower in JUNK_NAME_PATTERNS:
        return "generic_or_invalid_name"

    # Looks like a code (all alphanumeric, no spaces, starts with letters+digits)
    if re.match(r"^[A-Z]{2,4}\d{4,}$", name.strip()):
        return "looks_like_code"

    return None


def is_domain_name(name: str) -> Optional[str]:
    """
    Check if the company name is already a domain/URL.
    Returns the URL if so, None otherwise.
    """
    cleaned = name.strip().lower()
    # Matches patterns like "sulekha.com", "younity.in", "gadgetshalt.com"
    if re.match(r"^[a-z0-9][-a-z0-9]*\.[a-z]{2,6}(\.[a-z]{2,})?$", cleaned):
        return f"https://{cleaned}"
    return None


# ─── URL Resolution ──────────────────────────────────────────────────────────

def _simplify_name(name: str) -> str:
    """Simplify company name for domain matching: lowercase, remove suffixes."""
    s = name.lower()
    for suffix in [
        " pvt. ltd.", " pvt ltd.", " pvt. ltd", " pvt ltd",
        " private limited", " limited", " ltd.", " ltd",
        " llp", " inc.", " inc", " india", " group",
        " services", " solutions", " technologies", " technology",
    ]:
        s = s.replace(suffix, "")
    s = re.sub(r"[^a-z0-9]", "", s)  # keep only alphanumeric
    return s


def _score_url(url: str, company_name: str) -> int:
    """Score a URL for how likely it is the official website. Higher = better."""
    score = 0
    parsed = urlparse(url)
    domain = parsed.netloc.lower()

    # Blocklist check — return -1 to exclude
    for blocked in DIRECTORY_BLOCKLIST:
        if blocked in domain:
            return -1

    # Prefer Indian TLDs
    for tld in PREFERRED_TLDS:
        if domain.endswith(tld):
            score += 20
            break

    # Prefer .com
    if domain.endswith(".com"):
        score += 10

    # Prefer domains containing the simplified company name
    simplified = _simplify_name(company_name)
    domain_clean = re.sub(r"[^a-z0-9]", "", domain)
    if simplified and simplified in domain_clean:
        score += 30

    # Prefer shorter domains (less likely to be subpages of directories)
    if len(domain) < 25:
        score += 5

    # Prefer HTTPS
    if parsed.scheme == "https":
        score += 2

    return score


def resolve_company_url(
    name: str,
    url_cache: dict,
    ua: UserAgent,
) -> dict:
    """
    Resolve a company name to its official website URL using DuckDuckGo.
    Returns {"url": str|None, "directory_url": str|None, "cached": bool}
    """
    cache_key = _simplify_name(name) or name.lower().strip()

    # Check cache first
    if cache_key in url_cache:
        cached = url_cache[cache_key]
        return {
            "url": cached.get("url"),
            "directory_url": cached.get("directory_url"),
            "cached": True,
        }

    # Check if name is already a domain
    direct_url = is_domain_name(name)
    if direct_url:
        result = {"url": direct_url, "directory_url": None}
        url_cache[cache_key] = result
        return {**result, "cached": False}

    # Search DuckDuckGo
    official_url = None
    directory_url = None

    for attempt in range(MAX_RETRIES + 1):
        try:
            with DDGS() as ddgs:
                results = list(ddgs.text(
                    f"{name} India official website",
                    max_results=5,
                    region="in-en",
                ))

            if not results:
                break

            # Score and rank results
            scored = []
            for r in results:
                href = r.get("href", "")
                if not href:
                    continue

                s = _score_url(href, name)

                # Check if it's an Indian directory (save for fallback)
                parsed_domain = urlparse(href).netloc.lower()
                for d in INDIAN_DIRECTORIES:
                    if d in parsed_domain and not directory_url:
                        directory_url = href

                if s >= 0:
                    scored.append((s, href))

            scored.sort(key=lambda x: x[0], reverse=True)
            if scored:
                official_url = scored[0][1]

            break  # Success, no retry needed

        except Exception as e:
            if attempt < MAX_RETRIES:
                wait = SEARCH_DELAY_SECONDS * (2 ** attempt) + random.random()
                logger.warning(f"Search failed for '{name}', retrying in {wait:.1f}s: {e}")
                time.sleep(wait)
            else:
                logger.error(f"Search failed for '{name}' after {MAX_RETRIES + 1} attempts: {e}")

    # Throttle between searches
    time.sleep(SEARCH_DELAY_SECONDS + random.uniform(0, 1))

    result = {"url": official_url, "directory_url": directory_url}
    url_cache[cache_key] = result
    return {**result, "cached": False}


# ─── Page Fetching ───────────────────────────────────────────────────────────

async def _fetch_with_httpx(
    url: str,
    client: httpx.AsyncClient,
    semaphore: asyncio.Semaphore,
) -> Optional[str]:
    """Fetch a page using httpx. Returns HTML string or None."""
    async with semaphore:
        try:
            resp = await client.get(url, timeout=15.0, follow_redirects=True)
            if resp.status_code == 200:
                return resp.text
            if resp.status_code in (403, 503):
                return None  # Signal to try cloudscraper
        except Exception:
            pass
    return None


def _fetch_with_cloudscraper(url: str, ua: UserAgent) -> Optional[str]:
    """Fetch a page using cloudscraper for Cloudflare bypass. Returns HTML or None."""
    try:
        scraper = cloudscraper.create_scraper(
            browser={"browser": "chrome", "platform": "linux", "desktop": True}
        )
        scraper.headers.update({"User-Agent": ua.random})
        resp = scraper.get(url, timeout=20)
        if resp.status_code == 200:
            return resp.text
    except Exception:
        pass
    return None


async def _fetch_with_browser(url: str, semaphore: asyncio.Semaphore) -> Optional[str]:
    """Fetch a page using a real browser via crawl4ai. Returns HTML or None."""
    try:
        from crawl4ai import AsyncWebCrawler, BrowserConfig, CrawlerRunConfig

        async with semaphore:
            browser_cfg = BrowserConfig(headless=True)
            run_cfg = CrawlerRunConfig()
            async with AsyncWebCrawler(config=browser_cfg) as crawler:
                result = await crawler.arun(url=url, config=run_cfg)
                if result.success:
                    return result.html
    except ImportError:
        logger.warning("crawl4ai not available, skipping browser fallback")
    except Exception as e:
        logger.debug(f"Browser fetch failed for {url}: {e}")
    return None


async def fetch_page(
    url: str,
    http_client: httpx.AsyncClient,
    http_sem: asyncio.Semaphore,
    browser_sem: asyncio.Semaphore,
    ua: UserAgent,
) -> Optional[str]:
    """
    Three-tier page fetcher:
    1. httpx (fast, async)
    2. cloudscraper (Cloudflare bypass)
    3. crawl4ai browser (JS rendering + stealth)
    Returns HTML string or None.
    """
    # Tier 1: httpx
    html = await _fetch_with_httpx(url, http_client, http_sem)
    if html and len(html) > 500:
        return html

    # Tier 2: cloudscraper (sync, run in executor)
    loop = asyncio.get_event_loop()
    html = await loop.run_in_executor(None, _fetch_with_cloudscraper, url, ua)
    if html and len(html) > 500:
        return html

    # Tier 3: browser fallback
    html = await _fetch_with_browser(url, browser_sem)
    if html and len(html) > 500:
        return html

    return None


def _discover_subpages(html: str, base_url: str) -> dict:
    """
    Parse homepage HTML to find about and contact page URLs.
    Returns {"about_url": str|None, "contact_url": str|None}
    """
    result = {"about_url": None, "contact_url": None}
    try:
        soup = BeautifulSoup(html, "lxml")
        links = soup.find_all("a", href=True)

        about_keywords = ["about", "company", "who we are", "our story", "who-we-are"]
        contact_keywords = ["contact", "reach us", "get in touch", "reach-us"]

        for link in links:
            href = link.get("href", "").strip()
            text = link.get_text(strip=True).lower()
            href_lower = href.lower()

            if not result["about_url"]:
                if any(kw in text for kw in about_keywords) or any(kw in href_lower for kw in ["about", "company", "who-we"]):
                    result["about_url"] = urljoin(base_url, href)

            if not result["contact_url"]:
                if any(kw in text for kw in contact_keywords) or any(kw in href_lower for kw in ["contact", "reach", "get-in-touch"]):
                    result["contact_url"] = urljoin(base_url, href)

            if result["about_url"] and result["contact_url"]:
                break

    except Exception:
        pass

    return result


async def fetch_company_pages(
    base_url: str,
    http_client: httpx.AsyncClient,
    http_sem: asyncio.Semaphore,
    browser_sem: asyncio.Semaphore,
    ua: UserAgent,
    page_cache: dict,
) -> dict:
    """
    Fetch homepage + about page + contact page for a company.
    Returns {"homepage": str|None, "about_page": str|None, "contact_page": str|None}
    Uses page_cache keyed by URL to avoid refetching.
    """
    pages = {"homepage": None, "about_page": None, "contact_page": None}

    # Random delay before scraping
    await asyncio.sleep(random.uniform(*REQUEST_DELAY_RANGE))

    # Fetch homepage
    if base_url in page_cache:
        pages["homepage"] = page_cache[base_url]
    else:
        pages["homepage"] = await fetch_page(base_url, http_client, http_sem, browser_sem, ua)
        if pages["homepage"]:
            page_cache[base_url] = pages["homepage"]

    if not pages["homepage"]:
        return pages

    # Discover about/contact pages from homepage links
    subpages = _discover_subpages(pages["homepage"], base_url)

    # Try discovered URLs first, then fall back to common paths
    about_urls = []
    if subpages["about_url"]:
        about_urls.append(subpages["about_url"])
    about_urls.extend([urljoin(base_url, p) for p in ABOUT_PATHS])

    contact_urls = []
    if subpages["contact_url"]:
        contact_urls.append(subpages["contact_url"])
    contact_urls.extend([urljoin(base_url, p) for p in CONTACT_PATHS])

    # Deduplicate URLs
    seen = {base_url}

    # Fetch about page (try first 3 candidates)
    for url in about_urls[:3]:
        if url in seen:
            continue
        seen.add(url)
        if url in page_cache:
            pages["about_page"] = page_cache[url]
            break
        html = await fetch_page(url, http_client, http_sem, browser_sem, ua)
        if html and len(html) > 500:
            pages["about_page"] = html
            page_cache[url] = html
            break
        await asyncio.sleep(random.uniform(0.5, 1.5))

    # Fetch contact page (try first 3 candidates)
    for url in contact_urls[:3]:
        if url in seen:
            continue
        seen.add(url)
        if url in page_cache:
            pages["contact_page"] = page_cache[url]
            break
        html = await fetch_page(url, http_client, http_sem, browser_sem, ua)
        if html and len(html) > 500:
            pages["contact_page"] = html
            page_cache[url] = html
            break
        await asyncio.sleep(random.uniform(0.5, 1.5))

    return pages


# ─── Data Extraction ─────────────────────────────────────────────────────────

# Regex patterns
EMAIL_REGEX = re.compile(
    r"[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}",
    re.IGNORECASE,
)
GSTIN_REGEX = re.compile(
    r"\d{2}[A-Z]{5}\d{4}[A-Z][A-Z\d]Z[A-Z\d]"
)
CIN_REGEX = re.compile(
    r"[A-Z]\d{5}[A-Z]{2}\d{4}[A-Z]{3}\d{6}"
)
PIN_CODE_REGEX = re.compile(r"\b[1-9]\d{5}\b")

# False-positive email filters
EMAIL_BLACKLIST_DOMAINS = [
    "example.com", "sentry.io", "wixpress.com", "googleapis.com",
    "w3.org", "schema.org", "ogp.me", "facebook.com",
    "apple.com", "google.com", "mozilla.org",
]
EMAIL_BLACKLIST_PATTERNS = [
    r".*@\dx\..*",           # like name@2x.png
    r".*\.(png|jpg|jpeg|gif|svg|webp|ico)$",  # image filenames
    r".*\.(js|css|woff|ttf|eot)$",            # asset filenames
]


def _extract_emails(html: str) -> list[str]:
    """Extract email addresses from HTML. Returns deduplicated list."""
    emails = set()

    # From mailto: links
    try:
        soup = BeautifulSoup(html, "lxml")
        for a in soup.find_all("a", href=True):
            href = a["href"]
            if href.startswith("mailto:"):
                email = href.replace("mailto:", "").split("?")[0].strip().lower()
                if "@" in email:
                    emails.add(email)
    except Exception:
        pass

    # From text content via regex
    raw_text = ""
    try:
        raw_text = BeautifulSoup(html, "lxml").get_text(separator=" ")
    except Exception:
        raw_text = html

    for match in EMAIL_REGEX.finditer(raw_text):
        emails.add(match.group().lower())

    # Also check raw HTML for obfuscated emails
    for match in EMAIL_REGEX.finditer(html):
        emails.add(match.group().lower())

    # Filter out false positives
    filtered = []
    for email in emails:
        domain = email.split("@")[-1]
        if domain in EMAIL_BLACKLIST_DOMAINS:
            continue
        if any(re.match(pat, email) for pat in EMAIL_BLACKLIST_PATTERNS):
            continue
        # Must have a reasonable TLD
        tld = domain.split(".")[-1]
        if len(tld) < 2 or len(tld) > 10:
            continue
        filtered.append(email)

    return sorted(set(filtered))


def _extract_phones(html: str) -> list[str]:
    """Extract phone numbers from HTML using Google's phonenumbers library."""
    phones = set()
    text = ""

    try:
        soup = BeautifulSoup(html, "lxml")

        # From schema.org / itemProp="telephone"
        for el in soup.find_all(attrs={"itemprop": "telephone"}):
            tel = el.get_text(strip=True)
            if tel:
                try:
                    parsed = phonenumbers.parse(tel, DEFAULT_REGION)
                    if phonenumbers.is_valid_number(parsed):
                        formatted = phonenumbers.format_number(
                            parsed, phonenumbers.PhoneNumberFormat.INTERNATIONAL
                        )
                        phones.add(formatted)
                except Exception:
                    pass

        # From tel: links
        for a in soup.find_all("a", href=True):
            href = a["href"]
            if href.startswith("tel:"):
                tel = href.replace("tel:", "").strip()
                try:
                    parsed = phonenumbers.parse(tel, DEFAULT_REGION)
                    if phonenumbers.is_valid_number(parsed):
                        formatted = phonenumbers.format_number(
                            parsed, phonenumbers.PhoneNumberFormat.INTERNATIONAL
                        )
                        phones.add(formatted)
                except Exception:
                    pass

        # From JSON-LD structured data
        for script in soup.find_all("script", type="application/ld+json"):
            try:
                ld = json.loads(script.string or "")
                if isinstance(ld, dict):
                    for key in ["telephone", "phone", "contactPoint"]:
                        val = ld.get(key)
                        if isinstance(val, str):
                            try:
                                parsed = phonenumbers.parse(val, DEFAULT_REGION)
                                if phonenumbers.is_valid_number(parsed):
                                    phones.add(phonenumbers.format_number(
                                        parsed, phonenumbers.PhoneNumberFormat.INTERNATIONAL
                                    ))
                            except Exception:
                                pass
                        elif isinstance(val, dict):
                            tel = val.get("telephone", "")
                            if tel:
                                try:
                                    parsed = phonenumbers.parse(tel, DEFAULT_REGION)
                                    if phonenumbers.is_valid_number(parsed):
                                        phones.add(phonenumbers.format_number(
                                            parsed, phonenumbers.PhoneNumberFormat.INTERNATIONAL
                                        ))
                                except Exception:
                                    pass
                        elif isinstance(val, list):
                            for item in val:
                                tel = item.get("telephone", "") if isinstance(item, dict) else ""
                                if tel:
                                    try:
                                        parsed = phonenumbers.parse(tel, DEFAULT_REGION)
                                        if phonenumbers.is_valid_number(parsed):
                                            phones.add(phonenumbers.format_number(
                                                parsed, phonenumbers.PhoneNumberFormat.INTERNATIONAL
                                            ))
                                    except Exception:
                                        pass
            except Exception:
                pass

        text = soup.get_text(separator=" ")
    except Exception:
        text = html

    # From page text using PhoneNumberMatcher
    try:
        matcher = phonenumbers.PhoneNumberMatcher(text, DEFAULT_REGION)
        for match in matcher:
            num = match.number
            if phonenumbers.is_valid_number(num):
                formatted = phonenumbers.format_number(
                    num, phonenumbers.PhoneNumberFormat.INTERNATIONAL
                )
                phones.add(formatted)
    except Exception:
        pass

    return sorted(phones)


def _extract_about(html: str) -> Optional[str]:
    """Extract main about/description text from HTML using trafilatura."""
    try:
        text = trafilatura.extract(html, favor_recall=True)
        if text and len(text.strip()) > 30:
            # Truncate to ~2000 chars to keep output manageable
            return text.strip()[:2000]
    except Exception:
        pass

    # Fallback: meta description
    try:
        soup = BeautifulSoup(html, "lxml")
        meta = soup.find("meta", attrs={"name": "description"})
        if meta and meta.get("content"):
            desc = meta["content"].strip()
            if len(desc) > 20:
                return desc
        # Also try og:description
        meta = soup.find("meta", attrs={"property": "og:description"})
        if meta and meta.get("content"):
            desc = meta["content"].strip()
            if len(desc) > 20:
                return desc
    except Exception:
        pass

    return None


def _extract_address(html: str) -> Optional[str]:
    """Extract physical address from HTML."""
    try:
        soup = BeautifulSoup(html, "lxml")

        # From schema.org address
        addr_el = soup.find(attrs={"itemprop": "address"})
        if addr_el:
            addr_text = addr_el.get_text(separator=", ", strip=True)
            if len(addr_text) > 10:
                return addr_text[:500]

        # From JSON-LD
        for script in soup.find_all("script", type="application/ld+json"):
            try:
                ld = json.loads(script.string or "")
                if isinstance(ld, dict):
                    addr = ld.get("address")
                    if isinstance(addr, dict):
                        parts = [
                            addr.get("streetAddress", ""),
                            addr.get("addressLocality", ""),
                            addr.get("addressRegion", ""),
                            addr.get("postalCode", ""),
                            addr.get("addressCountry", ""),
                        ]
                        full = ", ".join(p for p in parts if p)
                        if len(full) > 10:
                            return full[:500]
                    elif isinstance(addr, str) and len(addr) > 10:
                        return addr[:500]
            except Exception:
                pass

        # Look for elements containing Indian PIN codes near address-like content
        text = soup.get_text(separator="\n")
        for line in text.split("\n"):
            line = line.strip()
            if PIN_CODE_REGEX.search(line) and len(line) > 15 and len(line) < 300:
                # Likely an address line
                return line

    except Exception:
        pass

    return None


def _extract_gstin(html: str) -> Optional[str]:
    """Extract GSTIN from HTML text."""
    try:
        text = BeautifulSoup(html, "lxml").get_text(separator=" ")
        match = GSTIN_REGEX.search(text)
        if match:
            return match.group()
    except Exception:
        pass
    # Also search raw HTML (sometimes in hidden fields)
    match = GSTIN_REGEX.search(html)
    return match.group() if match else None


def _extract_cin(html: str) -> Optional[str]:
    """Extract CIN (Corporate Identity Number) from HTML text."""
    try:
        text = BeautifulSoup(html, "lxml").get_text(separator=" ")
        match = CIN_REGEX.search(text)
        if match:
            return match.group()
    except Exception:
        pass
    match = CIN_REGEX.search(html)
    return match.group() if match else None


def extract_all_info(pages: dict) -> dict:
    """
    Extract all contact info from fetched pages.
    pages: {"homepage": str|None, "about_page": str|None, "contact_page": str|None}
    Returns: {"emails": [], "phone_numbers": [], "about": str|None, "address": str|None, "gstin": str|None, "cin": str|None}
    """
    emails = set()
    phones = set()
    about = None
    address = None
    gstin = None
    cin = None

    all_html = []
    for key in ["homepage", "contact_page", "about_page"]:
        html = pages.get(key)
        if html:
            all_html.append(html)

    for html in all_html:
        for e in _extract_emails(html):
            emails.add(e)
        for p in _extract_phones(html):
            phones.add(p)

        if not gstin:
            gstin = _extract_gstin(html)
        if not cin:
            cin = _extract_cin(html)

    # About: prefer about_page, fallback to homepage
    if pages.get("about_page"):
        about = _extract_about(pages["about_page"])
    if not about and pages.get("homepage"):
        about = _extract_about(pages["homepage"])

    # Address: prefer contact_page, fallback to homepage
    if pages.get("contact_page"):
        address = _extract_address(pages["contact_page"])
    if not address and pages.get("homepage"):
        address = _extract_address(pages["homepage"])
    if not address and pages.get("about_page"):
        address = _extract_address(pages["about_page"])

    return {
        "emails": sorted(emails),
        "phone_numbers": sorted(phones),
        "about": about,
        "address": address,
        "gstin": gstin,
        "cin": cin,
    }


# ─── Directory Fallback ─────────────────────────────────────────────────────

def resolve_directory_url(name: str) -> Optional[str]:
    """Search for a company on JustDial/IndiaMART as a fallback."""
    try:
        with DDGS() as ddgs:
            results = list(ddgs.text(
                f'"{name}" site:justdial.com OR site:indiamart.com',
                max_results=3,
                region="in-en",
            ))
        for r in results:
            href = r.get("href", "")
            domain = urlparse(href).netloc.lower()
            if any(d in domain for d in INDIAN_DIRECTORIES):
                return href
    except Exception as e:
        logger.debug(f"Directory search failed for '{name}': {e}")

    time.sleep(SEARCH_DELAY_SECONDS)
    return None


# ─── Main Orchestrator ───────────────────────────────────────────────────────

async def _process_single_company(
    entry: dict,
    url_cache: dict,
    page_cache: dict,
    results_cache: dict,
    http_client: httpx.AsyncClient,
    http_sem: asyncio.Semaphore,
    browser_sem: asyncio.Semaphore,
    ua: UserAgent,
) -> dict:
    """Process a single company entry. Returns result dict."""
    cid = str(entry["id"])
    fname = entry["fname"]
    cleaned = clean_company_name(fname)

    # Check if already processed
    if cid in results_cache:
        logger.info(f"  [{cid}] '{cleaned}' — cached, skipping")
        return results_cache[cid]

    result = {
        "id": cid,
        "fname": fname,
        "website_url": None,
        "emails": [],
        "phone_numbers": [],
        "about": None,
        "address": None,
        "gstin": None,
        "cin": None,
        "source": "none",
        "status": "failed",
        "error": None,
    }

    # Check for junk name
    junk_reason = is_junk_name(cleaned)
    if junk_reason:
        result["status"] = "skipped"
        result["error"] = junk_reason
        logger.info(f"  [{cid}] '{cleaned}' — skipped ({junk_reason})")
        return result

    try:
        # Stage 1: Resolve URL (sync, runs in executor to not block event loop)
        loop = asyncio.get_event_loop()
        url_info = await loop.run_in_executor(
            None, resolve_company_url, cleaned, url_cache, ua
        )

        official_url = url_info.get("url")
        directory_url = url_info.get("directory_url")

        if official_url:
            result["website_url"] = official_url
            logger.info(f"  [{cid}] '{cleaned}' → {official_url}" + (" (cached)" if url_info["cached"] else ""))

            # Stage 2: Fetch pages
            pages = await fetch_company_pages(
                official_url, http_client, http_sem, browser_sem, ua, page_cache,
            )

            if any(pages.values()):
                # Stage 3: Extract info
                info = extract_all_info(pages)
                result.update(info)
                result["source"] = "official_website"

                # Determine status
                has_data = bool(info["emails"] or info["phone_numbers"] or info["about"])
                result["status"] = "success" if has_data else "partial"
            else:
                result["status"] = "partial"
                result["error"] = "could_not_fetch_pages"

        # Fallback to directory if no URL or no data extracted
        if result["status"] in ("failed", "partial") and not result["emails"] and not result["phone_numbers"]:
            dir_url = directory_url
            if not dir_url:
                dir_url = await loop.run_in_executor(None, resolve_directory_url, cleaned)

            if dir_url:
                result["website_url"] = result["website_url"] or dir_url
                pages = await fetch_company_pages(
                    dir_url, http_client, http_sem, browser_sem, ua, page_cache,
                )
                if any(pages.values()):
                    info = extract_all_info(pages)
                    # Merge — don't overwrite existing data
                    if not result["emails"]:
                        result["emails"] = info["emails"]
                    if not result["phone_numbers"]:
                        result["phone_numbers"] = info["phone_numbers"]
                    if not result["about"]:
                        result["about"] = info["about"]
                    if not result["address"]:
                        result["address"] = info["address"]
                    if not result["gstin"]:
                        result["gstin"] = info["gstin"]
                    if not result["cin"]:
                        result["cin"] = info["cin"]
                    result["source"] = "directory" if not official_url else "official_website+directory"

                    has_data = bool(result["emails"] or result["phone_numbers"] or result["about"])
                    result["status"] = "success" if has_data else "partial"

        if not result["website_url"]:
            result["error"] = "no_website_found"

    except Exception as e:
        result["status"] = "failed"
        result["error"] = str(e)
        logger.error(f"  [{cid}] '{cleaned}' — error: {e}")

    return result


async def scrape_companies(
    input_data: list[dict],
    start: Optional[int] = None,
    end: Optional[int] = None,
) -> dict:
    """
    Main scraper function.

    Args:
        input_data: List of {"id": str, "fname": str} dicts
        start: 1-based start index (inclusive). None = from beginning.
        end: 1-based end index (inclusive). None = to the end.

    Returns:
        Dict with "results", "skipped", "summary" keys.
    """
    total = len(input_data)

    # Validate and apply range
    if start is not None and start < 1:
        raise ValueError(f"start must be >= 1, got {start}")
    if end is not None and end > total:
        raise ValueError(f"end must be <= {total} (total entries), got {end}")
    if start is not None and end is not None and start > end:
        raise ValueError(f"start ({start}) must be <= end ({end})")

    s = (start - 1) if start else 0
    e = end if end else total
    batch = input_data[s:e]

    logger.info(f"Processing items {s + 1}–{e} of {total}")

    # Load caches
    url_cache = load_cache(URL_CACHE_FILE)
    results_cache = load_cache(RESULTS_CACHE_FILE)
    page_cache: dict = {}  # In-memory only (HTML is too large to persist)

    ua = UserAgent(browsers=["chrome", "firefox", "edge"], os=["linux", "windows", "macos"])

    # Counters
    stats = {"success": 0, "partial": 0, "failed": 0, "skipped": 0}
    all_results = []
    skipped_entries = []

    # Concurrency controls
    http_sem = asyncio.Semaphore(MAX_CONCURRENT_HTTP)
    browser_sem = asyncio.Semaphore(MAX_CONCURRENT_BROWSERS)

    async with httpx.AsyncClient(
        headers={"User-Agent": ua.random},
        follow_redirects=True,
        http2=True,
        limits=httpx.Limits(max_connections=MAX_CONCURRENT_HTTP, max_keepalive_connections=20),
    ) as http_client:

        # Process in internal batches
        for batch_start in range(0, len(batch), INTERNAL_BATCH_SIZE):
            batch_end = min(batch_start + INTERNAL_BATCH_SIZE, len(batch))
            sub_batch = batch[batch_start:batch_end]

            logger.info(
                f"--- Internal batch {batch_start // INTERNAL_BATCH_SIZE + 1}"
                f" ({batch_start + 1}–{batch_end} of {len(batch)} in current range) ---"
            )

            # Process companies sequentially for URL resolution (rate-limited)
            # but fetch pages concurrently
            tasks = []
            for entry in sub_batch:
                task = _process_single_company(
                    entry, url_cache, page_cache, results_cache,
                    http_client, http_sem, browser_sem, ua,
                )
                tasks.append(task)

            # Run with limited concurrency (3 at a time to balance
            # search rate limits with fetch concurrency)
            sem = asyncio.Semaphore(3)

            async def _throttled(coro):
                async with sem:
                    return await coro

            results = await asyncio.gather(*[_throttled(t) for t in tasks])

            for r in results:
                status = r.get("status", "failed")
                stats[status] = stats.get(status, 0) + 1

                if status == "skipped":
                    skipped_entries.append({
                        "id": r["id"],
                        "fname": r["fname"],
                        "reason": r.get("error", "unknown"),
                    })
                else:
                    all_results.append(r)

                # Update results cache
                results_cache[r["id"]] = r

            # Save caches after each internal batch
            save_cache(URL_CACHE_FILE, url_cache)
            save_cache(RESULTS_CACHE_FILE, results_cache)

            logger.info(
                f"--- Batch done. Running totals: "
                f"success={stats['success']}, partial={stats['partial']}, "
                f"failed={stats['failed']}, skipped={stats['skipped']} ---"
            )

    output = {
        "results": all_results,
        "skipped": skipped_entries,
        "summary": {
            "total_input": total,
            "processed_range": f"{s + 1}-{e}",
            "range_count": len(batch),
            "skipped": stats["skipped"],
            "success": stats["success"],
            "partial": stats["partial"],
            "failed": stats["failed"],
        },
    }

    logger.info(f"Done. Summary: {json.dumps(output['summary'], indent=2)}")
    return output


def scrape_companies_sync(
    input_data: list[dict],
    start: Optional[int] = None,
    end: Optional[int] = None,
) -> dict:
    """
    Synchronous wrapper for scrape_companies().
    Use this when calling from non-async code.

    Args:
        input_data: List of {"id": str, "fname": str} dicts
        start: 1-based start index (inclusive)
        end: 1-based end index (inclusive)

    Returns:
        Dict with "results", "skipped", "summary" keys.

    Example:
        import json
        data = json.load(open("companyDataM.json"))
        results = scrape_companies_sync(data, start=1, end=50)
        json.dump(results, open("results.json", "w"), indent=2)
    """
    return asyncio.run(scrape_companies(input_data, start, end))


# ─── CLI Entry Point ─────────────────────────────────────────────────────────

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Indian Company Contact Scraper — scrape emails, phones, about, GSTIN, CIN",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Scrape companies 1 through 50
  python app.py --input companyDataM.json --output results.json --start 1 --end 50

  # Scrape companies 51 through 100
  python app.py --input companyDataM.json --output results.json --start 51 --end 100

  # Scrape from company 201 to end
  python app.py --input companyDataM.json --output results.json --start 201

  # Scrape all (no range)
  python app.py --input companyDataM.json --output results.json
        """,
    )
    parser.add_argument("--input", "-i", required=True, help="Path to input JSON file")
    parser.add_argument("--output", "-o", required=True, help="Path to output JSON file")
    parser.add_argument("--start", "-s", type=int, default=None, help="1-based start index (inclusive)")
    parser.add_argument("--end", "-e", type=int, default=None, help="1-based end index (inclusive)")

    args = parser.parse_args()

    # Load input
    logger.info(f"Loading input from {args.input}...")
    with open(args.input, "r", encoding="utf-8") as f:
        input_data = json.load(f)

    if not isinstance(input_data, list):
        logger.error("Input JSON must be an array of objects")
        sys.exit(1)

    logger.info(f"Loaded {len(input_data)} entries")

    # Run scraper
    output = scrape_companies_sync(input_data, start=args.start, end=args.end)

    # Save output
    with open(args.output, "w", encoding="utf-8") as f:
        json.dump(output, f, ensure_ascii=False, indent=2)

    logger.info(f"Results saved to {args.output}")

    # Print summary
    s = output["summary"]
    print(f"\n{'='*50}")
    print(f"SCRAPING COMPLETE")
    print(f"{'='*50}")
    print(f"Range:    {s['processed_range']} ({s['range_count']} items)")
    print(f"Success:  {s['success']}")
    print(f"Partial:  {s['partial']}")
    print(f"Failed:   {s['failed']}")
    print(f"Skipped:  {s['skipped']}")
    print(f"{'='*50}")


if __name__ == "__main__":
    main()
