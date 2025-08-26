#!/usr/bin/env python3
"""Strip // <vc-...> tags from YAML specs while preserving readable block style.
Also enforce a blank line between top-level fields and use '|-' for all string fields.
"""

from pathlib import Path
import re
import sys
import yaml

VC_FIELDS = ["vc-helpers", "vc-spec", "vc-code", "vc-preamble", "vc-postamble"]

class LiteralDumper(yaml.SafeDumper):
    pass

def str_representer(dumper, data):
    # Always use literal block style for strings
    return dumper.represent_scalar('tag:yaml.org,2002:str', data, style='|')

LiteralDumper.add_representer(str, str_representer)

TAG_OPEN_RE = re.compile(r"^\s*//\s*<vc-[^>]+>\s*$", re.MULTILINE)
TAG_CLOSE_RE = re.compile(r"^\s*//\s*</vc-[^>]+>\s*$", re.MULTILINE)


def strip_tags_from_content(content: str) -> str:
    # Remove opening and closing tag lines, then trim trailing/leading blank lines
    content = TAG_OPEN_RE.sub("", content)
    content = TAG_CLOSE_RE.sub("", content)
    # Collapse leading/trailing empty lines
    lines = content.splitlines()
    # strip leading empties
    while lines and lines[0].strip() == "":
        lines.pop(0)
    # strip trailing empties
    while lines and lines[-1].strip() == "":
        lines.pop()
    return "\n".join(lines)


def dump_with_format(data: dict) -> str:
    # Manually render in the desired order with consistent formatting
    ordered_keys = [
        "vc-preamble",
        "vc-helpers",
        "vc-spec",
        "vc-code",
        "vc-postamble",
    ]
    parts: list[str] = []
    for key in ordered_keys:
        value = data.get(key)
        if value is None:
            value = ""
        if not isinstance(value, str):
            value = str(value)
        parts.append(f"{key}: |-")
        if value:
            for line in value.splitlines():
                parts.append(f"  {line}")
        # blank line between fields
        parts.append("")
    # Trim trailing blank line and ensure trailing newline
    text = "\n".join(parts).rstrip() + "\n"
    return text


def process_file(path: Path) -> bool:
    try:
        with path.open('r') as f:
            data = yaml.safe_load(f)
        if not isinstance(data, dict):
            return False
        changed = False
        for key in VC_FIELDS:
            value = data.get(key)
            if isinstance(value, str):
                # Normalize None to empty string
                new_value = value
                if key in ("vc-helpers", "vc-spec", "vc-code") and value:
                    new_value = strip_tags_from_content(value)
                # Ensure no trailing spaces on lines
                new_value = "\n".join([ln.rstrip() for ln in new_value.splitlines()])
                if new_value != value:
                    data[key] = new_value
                    changed = True
        # Write back even if not changed to normalize formatting
        out_text = dump_with_format(data)
        with path.open('w') as f:
            f.write(out_text)
        return True
    except Exception as e:
        print(f"✗ {path}: {e}")
        return False


def main():
    base = Path("benchmarks/vericoding_dafny/dafnybench/yaml")
    if len(sys.argv) > 1:
        base = Path(sys.argv[1])
    if not base.exists():
        print(f"Path not found: {base}")
        sys.exit(1)
    files = []
    if base.is_file():
        files = [base]
    else:
        files = list(base.rglob("*.yaml")) + list(base.rglob("*.yml"))
    print(f"Processing {len(files)} YAML file(s) under {base}...")
    modified = 0
    for p in files:
        if process_file(p):
            modified += 1
            print(f"✓ Formatted: {p}")
    print(f"Done. Modified {modified} files.")

if __name__ == '__main__':
    main()
