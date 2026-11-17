"""Mount canonical repository Markdown in MkDocs without copying it."""

from __future__ import annotations

import posixpath
import re
from functools import lru_cache
from pathlib import Path
from urllib.parse import quote, unquote, urlsplit, urlunsplit

from mkdocs.structure.files import File

ROOT = Path(__file__).resolve().parent.parent
REPO_URL = "https://github.com/laurajoyhutchins/eth-disproof-rust"
SOURCE_DIRS = (
    "research",
    "rust/lean_eth_reference/docs",
    "rust/native_lean_backend",
    "rust/native_lean_backend/docs",
)
SINGLE_SOURCES = (
    "README.md",
    "CONTRIBUTING.md",
    "rust/lean_eth_reference/README.md",
)

LINK = re.compile(r'(?<!!)(\[[^\]]+\]\()(?P<href>[^\s)]+)(?P<title>\s+[^)]*)?(\))')
# Fenced code examples are not prose links.
FENCE = re.compile(r"(^\s*\x60{3,}.*?^\s*\x60{3,}[^\n]*(?:\n|$))", re.M | re.S)


@lru_cache(maxsize=1)
def source_paths() -> tuple[str, ...]:
    """Only curated Markdown is mounted, not the entire source repository."""
    sources = [ROOT / name for name in SINGLE_SOURCES]
    for name in SOURCE_DIRS:
        sources.extend(sorted((ROOT / name).glob("*.md")))
    result = tuple(sorted(path.relative_to(ROOT).as_posix() for path in sources))
    for rel in result:
        if not (ROOT / rel).is_file():
            raise FileNotFoundError(f"MkDocs source does not exist: {rel}")
    if len(result) != len(set(result)):
        raise ValueError("Duplicate virtual Markdown source")
    return result


def on_files(files, config, **kwargs):
    """Attach physical files using their original repo-relative source URI."""
    known = {file.src_uri for file in files}
    for rel in source_paths():
        if rel not in known:
            files.append(
                File(
                    path=rel,
                    src_dir=str(ROOT),
                    dest_dir=config["site_dir"],
                    use_directory_urls=config["use_directory_urls"],
                )
            )
    return files


def rewrite_source_links(markdown: str, src_uri: str) -> str:
    """Keep document links local; point non-document source links to GitHub.

    Truly missing links are deliberately not masked, so MkDocs can warn.
    """
    site_pages = set(source_paths())
    site_pages.add("index.md")

    def replace(match: re.Match[str]) -> str:
        href = match.group("href")
        if href.startswith(("#", "/", "//")):
            return match.group(0)
        parsed = urlsplit(href)
        if parsed.scheme or parsed.netloc or not parsed.path:
            return match.group(0)
        virtual = posixpath.normpath(
            posixpath.join(posixpath.dirname(src_uri), unquote(parsed.path))
        )
        if virtual.startswith("../") or virtual == "..":
            return match.group(0)
        if virtual in site_pages:
            return match.group(0)

        source = ROOT / virtual
        if source.is_file():
            kind = "blob"
        elif source.is_dir():
            kind = "tree"
        else:
            return match.group(0)

        destination = quote(virtual, safe="/")
        path = f"/laurajoyhutchins/eth-disproof-rust/{kind}/main/{destination}"
        replacement = urlunsplit(
            ("https", "github.com", path, parsed.query, parsed.fragment)
        )
        return match.group(1) + replacement + (match.group("title") or "") + match.group(4)

    chunks = FENCE.split(markdown)
    return "".join(
        chunk if index % 2 else LINK.sub(replace, chunk)
        for index, chunk in enumerate(chunks)
    )


def on_page_markdown(markdown, page, config, files):
    return rewrite_source_links(markdown, page.file.src_uri)
