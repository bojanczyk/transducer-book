#!/usr/bin/python3
"""Comments under the chapters of the web edition.

The site is a directory of static files, and it stays one: this is the single
moving part, a CGI script that the page fetches from. Everything about it is
shaped by where it has to run — www.mimuw.edu.pl, serving ~bojan/public_html —
so the constraints are worth writing down, because they are not obvious and
they are what rule out the usual answers:

  * PHP is switched off for user directories. /etc/apache2/mods-enabled/
    php8.4.conf ends with `<Directory /home/*/public_html> php_admin_flag
    engine Off`, so no .php file there will ever be more than a download.
  * CGI is on. mods-enabled/userdir.conf gives /home/staff/*/*/public_html
    `Options ... ExecCGI` and `AddHandler cgi-script .cgi .pl .py`, so a .py
    file with the execute bit and a shebang is a program. That is this file.
  * POST is allowed: `Require method GET POST OPTIONS`.
  * suexec runs it as bojan, not as www-data, so it can write in the home
    directory — which is where the comments go, deliberately outside
    public_html so that nothing can fetch the raw store, only what this script
    chooses to hand back.
  * Python 3.13, where the `cgi` module no longer exists (PEP 594 removed it).
    Hence the hand-rolled form parsing below; anything found on the web that
    starts `import cgi` will not run here.

The store is one JSONL file per page, appended under flock. There is no
database because a database is a daemon, and a daemon is not something a user
account on a shared web server gets to keep running.

    GET  comments.py?page=<slug>   -> {"comments": [ … ]}
    POST comments.py               -> {"comment": { … }}
         page=<slug>&name=<name>&text=<text>

Moderation is deliberately absent for now. When it is wanted, the store is
plain text with one comment per line: deleting a line deletes a comment, and
`grep -c . ~/transducer-comments/*.jsonl` is the traffic report.
"""

import fcntl
import json
import os
import re
import secrets
import sys
import time
import unicodedata
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import parse_qs

# Outside public_html on purpose: Apache serves that tree, and a .jsonl in it
# would hand anyone the whole store, including the IP addresses recorded with
# each comment. Under $HOME, the only way in is through this script.
STORE = Path.home() / "transducer-comments"

MAX_BODY = 16 * 1024      # bytes of POST we will read at all
MAX_TEXT = 4000           # characters of comment
MAX_NAME = 60             # characters of name
SLUG = re.compile(r"^[0-9a-z][0-9a-z-]{0,63}$")

# Two windows rather than one: the short window stops a jammed submit button
# and the runaway script, the long one stops the patient flood. Neither is
# moderation — they only keep one visitor from filling the disk before anyone
# notices.
RATE = [(300, 4), (3600, 20)]


def reply(obj, status="200 OK"):
    body = json.dumps(obj, ensure_ascii=False).encode()
    sys.stdout.buffer.write(
        f"Status: {status}\r\n"
        f"Content-Type: application/json; charset=utf-8\r\n"
        f"Content-Length: {len(body)}\r\n"
        f"X-Content-Type-Options: nosniff\r\n"
        f"Cache-Control: no-store\r\n\r\n".encode() + body)
    sys.exit(0)


def fail(message, status):
    reply({"error": message}, status)


def clean(s, limit):
    """Text as a person typed it, with everything that is not text removed.

    Control characters are dropped rather than escaped: they are invisible in
    the page and useful only for making one line of a JSONL file look like
    several. The page renders comments with textContent, so `<` and `&` are
    safe to keep and are kept — this is a book about formal languages, and
    people will want to write `a -> <b, c>`.
    """
    s = unicodedata.normalize("NFC", s)
    s = "".join(c for c in s if c == "\n" or not unicodedata.category(c).startswith("C"))
    s = re.sub(r"\n{3,}", "\n\n", s).strip()
    return s[:limit]


def page_exists(slug):
    """Whether the site really has that page.

    The check is the site itself — public_html/books/transducer/<slug>/ —
    rather than a list kept here, which would be one more thing to update
    whenever a chapter is added and would be wrong the first time someone
    forgot. It also means a made-up slug cannot open a file: no store is
    created for a page that does not exist.
    """
    return (Path(__file__).resolve().parent / slug / "index.html").is_file()


def who():
    """The visitor, for rate limiting only — never sent back to the page."""
    fwd = os.environ.get("HTTP_X_FORWARDED_FOR", "")
    return (fwd.split(",")[0].strip() or os.environ.get("REMOTE_ADDR", "?"))[:64]


def rate_ok(ip):
    STORE.mkdir(mode=0o700, exist_ok=True)
    path = STORE / ".rate.json"
    now = time.time()
    with open(path, "a+") as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        fh.seek(0)
        try:
            seen = json.loads(fh.read() or "{}")
        except ValueError:
            seen = {}
        longest = max(w for w, _ in RATE)
        mine = [t for t in seen.get(ip, []) if now - t < longest]
        if any(sum(1 for t in mine if now - t < w) >= n for w, n in RATE):
            return False
        mine.append(now)
        seen[ip] = mine
        # everyone else's expired timestamps go at the same time, so the file
        # stays the size of recent traffic rather than of all traffic ever
        seen = {k: [t for t in v if now - t < longest]
                for k, v in seen.items() if any(now - t < longest for t in v)}
        fh.seek(0)
        fh.truncate()
        fh.write(json.dumps(seen))
    return True


def read(slug):
    path = STORE / f"{slug}.jsonl"
    if not path.is_file():
        return []
    out = []
    with open(path, encoding="utf-8") as fh:
        fcntl.flock(fh, fcntl.LOCK_SH)
        for line in fh:
            try:
                c = json.loads(line)
            except ValueError:
                continue          # a torn line is skipped, not fatal
            out.append({k: c[k] for k in ("id", "name", "text", "at") if k in c})
    return out


def append(slug, comment):
    STORE.mkdir(mode=0o700, exist_ok=True)
    with open(STORE / f"{slug}.jsonl", "a", encoding="utf-8") as fh:
        fcntl.flock(fh, fcntl.LOCK_EX)
        fh.write(json.dumps(comment, ensure_ascii=False) + "\n")


def form():
    n = int(os.environ.get("CONTENT_LENGTH") or 0)
    if n > MAX_BODY:
        fail("that is too long", "413 Payload Too Large")
    raw = sys.stdin.buffer.read(n).decode("utf-8", "replace")
    return {k: v[0] for k, v in parse_qs(raw, keep_blank_values=True).items()}


def main():
    method = os.environ.get("REQUEST_METHOD", "GET")

    if method == "OPTIONS":
        reply({"ok": True})

    if method == "GET":
        slug = parse_qs(os.environ.get("QUERY_STRING", "")).get("page", [""])[0]
        if not SLUG.match(slug):
            fail("no such page", "400 Bad Request")
        reply({"comments": read(slug)})

    if method != "POST":
        fail("use GET or POST", "405 Method Not Allowed")

    f = form()
    slug = f.get("page", "")
    if not SLUG.match(slug) or not page_exists(slug):
        fail("no such page", "400 Bad Request")

    # A field no person can see and no person fills in. Bots fill in every
    # field they find, so a non-empty one is a bot; it is told the comment was
    # posted, and the comment is dropped, because a bot that is told it failed
    # comes straight back and tries something else.
    if f.get("website", "").strip():
        reply({"comment": {"id": "", "name": "", "text": "", "at": ""}})

    text = clean(f.get("text", ""), MAX_TEXT)
    if not text:
        fail("write something first", "400 Bad Request")
    name = clean(f.get("name", ""), MAX_NAME).replace("\n", " ") or "anonymous"

    if not rate_ok(who()):
        fail("that is a lot of comments in a short time — try again later",
             "429 Too Many Requests")

    comment = {"id": secrets.token_hex(8), "name": name, "text": text,
               "at": datetime.now(timezone.utc).isoformat(timespec="seconds")}
    append(slug, {**comment, "ip": who()})
    reply({"comment": comment})


if __name__ == "__main__":
    try:
        main()
    except SystemExit:
        raise
    except Exception:
        # A traceback on stdout would be served as the page's comments; the
        # detail belongs in Apache's error log, which is what stderr is.
        import traceback
        traceback.print_exc(file=sys.stderr)
        fail("the comment server is having a bad day", "500 Internal Server Error")
