#!/usr/bin/env python3
"""
Sync AI-related API keys from ~/.config/zsh into a local .env file safely.

Behavior:
- Scans text files under the given source directory (default: ~/.config/zsh).
- Parses simple `export VAR=VALUE` / `VAR=VALUE` assignments.
- Filters to AI/LLM provider keys and relevant endpoints.
- Updates/creates .env without printing secret values.
- Prints only the list of key NAMES that were added/updated.

Notes:
- Intentionally skips values that include shell expansions ($, `, $(), etc.).
- Last definition wins if the same key appears in multiple files.
"""

from __future__ import annotations

import argparse
import datetime as dt
import os
from pathlib import Path
import re
import shutil
from typing import Dict, Iterable, List, Tuple


DEFAULT_PREFIXES = [
    # Major LLM providers
    "OPENAI", "AZURE_OPENAI", "ANTHROPIC", "COHERE", "MISTRAL", "GROQ",
    "GOOGLE", "GEMINI", "HUGGINGFACEHUB", "HF", "REPLICATE", "OPENROUTER",
    "PERPLEXITY", "VOYAGE", "FIREWORKS", "AI21", "TOGETHER", "DEEPSEEK",
    "XAI", "STABILITY", "ELEVEN", "ELEVENLABS", "DEEPGRAM", "ASSEMBLYAI",
    # Useful tooling/search/observability
    "LANGSMITH", "WANDB", "TAVILY", "SERPAPI", "BROWSERLESS", "UNSTRUCTURED",
    "BING",
]

ALLOWED_SUFFIXES = [
    # Credentials / tokens
    "API_KEY", "API_TOKEN", "TOKEN", "KEY",
    # Endpoints / bases
    "API_URL", "BASE_URL", "API_BASE", "ENDPOINT", "API_ENDPOINT",
    # Orgs (for some providers)
    "ORG", "ORG_ID", "ORGANIZATION",
]

# Explicit allowlist for singletons not covered by prefix+suffix heuristics
EXTRA_ALLOW = {
    "HUGGINGFACEHUB_API_TOKEN",
    "WANDB_API_KEY",
    "GOOGLE_API_KEY",
    "OPENAI_API_BASE",
    "OPENAI_BASE_URL",
}

ASSIGN_RE = re.compile(r"^(?:export|typeset\s+-x|declare\s+-x)?\s*([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*)$")


def is_text_file(p: Path) -> bool:
    try:
        with p.open('rb') as f:
            chunk = f.read(1024)
        return b"\0" not in chunk
    except Exception:
        return False


def strip_outside_comments(s: str) -> str:
    out = []
    in_s = False
    in_d = False
    i = 0
    while i < len(s):
        c = s[i]
        if c == "'" and not in_d:
            in_s = not in_s
            out.append(c)
        elif c == '"' and not in_s:
            in_d = not in_d
            out.append(c)
        elif c == '#' and not in_s and not in_d:
            break  # comment starts
        else:
            out.append(c)
        i += 1
    return ''.join(out).rstrip()


def parse_assignment(line: str) -> Tuple[str, str] | None:
    line = line.strip()
    if not line or line.startswith('#'):
        return None
    m = ASSIGN_RE.match(line)
    if not m:
        return None
    key, raw_val = m.group(1), m.group(2)
    # Remove comments outside quotes
    val = strip_outside_comments(raw_val).strip()
    if not val:
        return None
    # Skip values with expansions or subshells (keep it static only)
    if any(sym in val for sym in ('`', '$(', '${', '$')):
        return None
    return key, val


def is_ai_key(key: str) -> bool:
    if key in EXTRA_ALLOW:
        return True
    for prefix in DEFAULT_PREFIXES:
        if key.startswith(prefix + "_"):
            for suf in ALLOWED_SUFFIXES:
                if key.endswith("_" + suf) or key.endswith(suf):
                    return True
    return False


def collect_keys(src_dir: Path) -> Dict[str, str]:
    env_map: Dict[str, str] = {}
    for root, _, files in os.walk(src_dir):
        for name in sorted(files):
            p = Path(root) / name
            if not is_text_file(p):
                continue
            try:
                with p.open('r', encoding='utf-8', errors='ignore') as f:
                    for raw in f:
                        parsed = parse_assignment(raw)
                        if not parsed:
                            continue
                        k, v = parsed
                        if is_ai_key(k):
                            env_map[k] = v  # last wins
            except Exception:
                continue
    return env_map


def update_dotenv(dest: Path, new_pairs: Dict[str, str]) -> Tuple[List[str], List[str]]:
    """
    Merge keys into .env.
    Returns (added_keys, updated_keys).
    """
    existing: List[str] = []
    if dest.exists():
        existing = dest.read_text(encoding='utf-8', errors='ignore').splitlines()

    # Remove any existing definitions for keys we'll manage
    managed = set(new_pairs.keys())

    def line_key(line: str) -> str | None:
        m = ASSIGN_RE.match(line.strip())
        return m.group(1) if m else None

    filtered: List[str] = []
    prev_keys: Dict[str, str] = {}
    for line in existing:
        k = line_key(line)
        if k and k in managed:
            prev_keys[k] = line
            continue  # drop old definition
        filtered.append(line)

    added, updated = [], []
    banner = f"# --- begin synced ai keys ({dt.datetime.now().strftime('%Y-%m-%d %H:%M:%S')}) ---"
    filtered.append(banner)
    for k in sorted(new_pairs):
        if k in prev_keys:
            updated.append(k)
        else:
            added.append(k)
        filtered.append(f"{k}={new_pairs[k]}")
    filtered.append("# --- end synced ai keys ---")

    dest.write_text('\n'.join(filtered) + '\n', encoding='utf-8')
    return added, updated


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--src', type=Path, default=Path(os.path.expanduser('~/.config/zsh')))
    parser.add_argument('--dest', type=Path, default=Path('.env'))
    args = parser.parse_args()

    src = args.src
    dest = args.dest

    if not src.exists() or not src.is_dir():
        print(f"Source directory not found: {src}")
        return 1

    env_map = collect_keys(src)
    if not env_map:
        print("No AI-related keys found to sync.")
        return 0

    # Backup existing .env
    if dest.exists():
        ts = dt.datetime.now().strftime('%Y%m%d-%H%M%S')
        backup = dest.with_suffix(dest.suffix + f'.bak.{ts}')
        shutil.copy2(dest, backup)

    added, updated = update_dotenv(dest, env_map)

    print("Synced keys into .env")
    if added:
        print("Added:")
        for k in added:
            print(f"  - {k}")
    if updated:
        print("Updated:")
        for k in updated:
            print(f"  - {k}")
    print(f"Total: {len(added) + len(updated)} keys")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

