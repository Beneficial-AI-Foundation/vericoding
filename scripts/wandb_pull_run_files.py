#!/usr/bin/env python3
"""
Download all files associated with a Weights & Biases run into a local folder,
preserving the paths so the original Lake/Lean project structure is recreated.

- Downloads run files (run.files()) directly into the output root, honoring subpaths.
- Optionally downloads logged/used artifacts and merges their contents into the
  output root, preserving each entry's path inside the artifact.

Examples
  uv run scripts/wandb_pull_run_files.py \
    --run entity/project/abc123 \
    --out wandb_exports/abc123

  uv run scripts/wandb_pull_run_files.py \
    --run https://wandb.ai/entity/project/runs/abc123 \
    --out ./exports/abc123 --artifact-mode flatten --filter-prefix benchmarks/

Auth
  Requires WANDB_API_KEY set in the environment (or logged-in wandb CLI).
"""
from __future__ import annotations

import argparse
import os
import re
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Iterable, Tuple, Optional

import wandb  # type: ignore
from wandb.apis.public import Run  # type: ignore
from typing import Any as _Any  # runtime-only

try:
    from tqdm import tqdm  # type: ignore
except Exception:  # pragma: no cover
    def tqdm(x, **kwargs):  # type: ignore
        return x


RUN_URL_RE = re.compile(r"https?://wandb\.ai/(?P<entity>[^/]+)/(?P<project>[^/]+)/runs/(?P<run>[^/?#]+)")


def parse_run_ref(ref: str, default_entity: Optional[str], default_project: Optional[str]) -> Tuple[str, str, str]:
    """Parse a run reference which can be:
    - entity/project/run_id
    - https://wandb.ai/entity/project/runs/run_id
    - run_id (uses defaults from env or args)
    """
    m = RUN_URL_RE.match(ref)
    if m:
        return m.group("entity"), m.group("project"), m.group("run")

    parts = ref.strip().split("/")
    if len(parts) == 3:
        return parts[0], parts[1], parts[2]
    if len(parts) == 1:
        if not (default_entity and default_project):
            raise SystemExit("Provide --entity and --project when using a bare run id")
        return default_entity, default_project, parts[0]
    raise SystemExit(f"Unrecognized run reference: {ref}")


def ensure_dir(p: Path) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)


def copy_file(src: Path, dst: Path, overwrite: bool = False) -> None:
    ensure_dir(dst)
    if dst.exists():
        if overwrite:
            if dst.is_file():
                dst.unlink()
            else:
                shutil.rmtree(dst)
        else:
            # If file exists with same size, skip; otherwise error for visibility
            try:
                if dst.stat().st_size == src.stat().st_size:
                    return
            except Exception:
                pass
            print(f"Skipping existing file: {dst}")
            return
    shutil.copy2(src, dst)


def download_run_files(run: Run, out_root: Path, filter_prefix: Optional[str], overwrite: bool) -> int:
    count = 0
    print("⤵️  Downloading run files...")
    for f in tqdm(list(run.files())):
        rel = f.name  # may include subdirs, e.g. "code/file.py"
        if filter_prefix and not rel.startswith(filter_prefix):
            continue
        try:
            # Ensure parent directory exists explicitly (mkdir -p of dirname)
            rel_path = out_root / rel
            ensure_dir(rel_path)
            # wandb creates subdirs under root based on f.name
            f.download(root=str(out_root), replace=overwrite)
            count += 1
        except Exception as e:
            print(f"⚠️  Failed to download {rel}: {e}")
    return count


def iter_unique_artifacts(run: Run, which: str) -> Iterable[_Any]:
    seen = set()
    if which in ("logged", "both"):
        for a in run.logged_artifacts():
            if a.id not in seen:
                seen.add(a.id)
                yield a
    if which in ("used", "both"):
        for a in run.used_artifacts():
            if a.id not in seen:
                seen.add(a.id)
                yield a


def download_artifacts(
    run: Run,
    out_root: Path,
    which: str,
    artifact_mode: str,
    filter_prefix: Optional[str],
    overwrite: bool,
) -> int:
    if which == "none":
        return 0

    count = 0
    print(f"⤵️  Downloading {which} artifacts (mode: {artifact_mode})...")
    with tempfile.TemporaryDirectory() as tmpd:
        tmp = Path(tmpd)
        for a in tqdm(list(iter_unique_artifacts(run, which))):
            try:
                downloaded_path = Path(a.download(root=str(tmp)))
            except Exception as e:
                print(f"⚠️  Failed to download artifact {a.name}: {e}")
                continue

            # Flatten: merge each entry at its manifest path into out_root
            # Subdir: keep under out_root/artifacts/<artifact_name:ver>/
            if artifact_mode == "subdir":
                base = out_root / "artifacts" / downloaded_path.name
                base.mkdir(parents=True, exist_ok=True)
                # Copy everything as-is
                for p in downloaded_path.rglob('*'):
                    if p.is_file():
                        rel = p.relative_to(downloaded_path)
                        dst = base / rel
                        if filter_prefix and not str(rel).startswith(filter_prefix):
                            continue
                        copy_file(p, dst, overwrite)
                        count += 1
            else:  # flatten
                # Use manifest to preserve original internal paths
                try:
                    entries = a.manifest.entries
                except Exception:
                    # Fallback: walk files
                    entries = {str(p.relative_to(downloaded_path)): None for p in downloaded_path.rglob('*') if p.is_file()}

                for rel, _entry in entries.items():
                    if filter_prefix and not str(rel).startswith(filter_prefix):
                        continue
                    src = downloaded_path / rel
                    if not src.exists():
                        # Some manifests have symlinks or dirs; skip
                        continue
                    dst = out_root / rel
                    # Ensure parent directory exists explicitly
                    ensure_dir(dst)
                    copy_file(src, dst, overwrite)
                    count += 1
    return count


def maybe_promote_code_root(out_root: Path) -> Optional[Path]:
    """If the run was captured under a top-level "code/" directory (W&B default
    for code-saving), and no lakefile exists at the root, promote "code/" to
    the root by merging its contents into `out_root`.

    Returns the new project root if promotion happened, else None.
    """
    code_dir = out_root / "code"
    lake_at_root = out_root / "lakefile.lean"
    lake_in_code = code_dir / "lakefile.lean"
    if code_dir.is_dir() and lake_in_code.exists() and not lake_at_root.exists():
        print("ℹ️  Detected Lake project under 'code/'. Promoting to export root…")
        for p in code_dir.rglob('*'):
            if p.is_file():
                rel = p.relative_to(code_dir)
                dst = out_root / rel
                ensure_dir(dst)
                copy_file(p, dst, overwrite=True)
        # Try to remove now-empty 'code' directory
        try:
            shutil.rmtree(code_dir)
        except Exception:
            pass
        return out_root
    return None


def main() -> None:
    p = argparse.ArgumentParser(description="Export a W&B run's files and artifacts, preserving folder structure.")
    p.add_argument("--run", required=True, help="Run ref: entity/project/<run_id> or full W&B URL or bare run_id")
    p.add_argument("--entity", default=os.getenv("WANDB_ENTITY"), help="Default entity (if --run is only a run_id)")
    p.add_argument("--project", default=os.getenv("WANDB_PROJECT", "vericoding"), help="Default project (if --run is only a run_id)")
    p.add_argument("--out", default=None, help="Output directory root (default: wandb_exports/<run_id>)")
    p.add_argument("--artifact-mode", choices=["flatten", "subdir"], default="flatten", help="How to place artifact contents")
    p.add_argument("--artifacts", choices=["none", "logged", "used", "both"], default="both", help="Which artifacts to include")
    p.add_argument("--filter-prefix", default=None, help="Only include files whose path starts with this prefix (e.g., 'benchmarks/')")
    p.add_argument("--overwrite", action="store_true", help="Overwrite files if they already exist")
    # Enabled by default; provide an opt-out flag
    p.set_defaults(promote_code_root=True)
    p.add_argument("--no-promote-code-root", dest="promote_code_root", action="store_false",
                   help="Disable promoting 'code/' Lake project to export root")

    args = p.parse_args()

    if not os.getenv("WANDB_API_KEY"):
        print("⚠️  WANDB_API_KEY not set. If wandb CLI is logged in, API may still work.")

    entity, project, run_id = parse_run_ref(args.run, args.entity, args.project)

    api = wandb.Api()
    run_path = f"{entity}/{project}/{run_id}"
    print(f"Fetching run: {run_path} ...")
    run = api.run(run_path)

    out_root = Path(args.out or (Path("wandb_exports") / run.id))
    out_root.mkdir(parents=True, exist_ok=True)
    print(f"Output directory: {out_root}")

    n_files = download_run_files(run, out_root, args.filter_prefix, args.overwrite)
    n_art = download_artifacts(run, out_root, args.artifacts, args.artifact_mode, args.filter_prefix, args.overwrite)

    # Optionally promote code root if Lake project exists under 'code/'
    if args.promote_code_root:
        maybe_promote_code_root(out_root)

    print(f"\n✅ Export complete: {n_files} run files, {n_art} artifact files → {out_root}")
    # Optional: show a hint for Lake
    lakefile = out_root / "lakefile.lean"
    if lakefile.exists():
        print("Detected Lake project (lakefile.lean present). You can try: \n  cd" , out_root, "&& lake build")


if __name__ == "__main__":
    main()
