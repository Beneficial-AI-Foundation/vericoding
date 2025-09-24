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
from pathlib import Path
from typing import Tuple, Optional

import wandb  # type: ignore

DEFAULT_DIR = "wandb_exports"
RESULTS_TABLE = "detailed_results.table.json"

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


def main() -> None:
    p = argparse.ArgumentParser(description="Export a W&B run's files and artifacts, preserving folder structure.")
    p.add_argument("--run", required=True, help="Run ref: entity/project/<run_id> or full W&B URL or bare run_id")
    p.add_argument("--out", default=None, help="Output directory root (default: wandb_exports/<run_id>)")
    p.add_argument("--overwrite", action="store_true", help="Overwrite files if they already exist")

    args = p.parse_args()

    if not os.getenv("WANDB_API_KEY"):
        print("⚠️  WANDB_API_KEY not set. If wandb CLI is logged in, API may still work.")

    entity, project, run_id = parse_run_ref(args.run, os.getenv("WANDB_ENTITY"), os.getenv("WANDB_PROJECT", "vericoding"))

    out_root = Path(args.out or (Path(DEFAULT_DIR) / run_id))
    out_root.mkdir(parents=True, exist_ok=True)
    print(f"Output directory: {out_root}")
    
    outFile = out_root / RESULTS_TABLE

    if (args.overwrite or not outFile.exists()):
        api = wandb.Api()
        run_path = f"{entity}/{project}/{run_id}"
        print(f"Fetching run: {run_path} ...")
        try:
            run = api.run(run_path)

            name = ""
            for f in run.files():
                if "detailed_results" in f.name:
                    name = f.name
                    f.download(root = out_root, replace=args.overwrite, exist_ok=True)
            
            
            if len(name) == 0:
                print(f"No detailed results table found for {run_id}")
            else:
                os.rename(out_root / name, out_root / RESULTS_TABLE)
                os.rmdir(out_root / "media" / "table")
                os.rmdir(out_root / "media")
        except Exception:
            print(f"WandB retrieval of {run_id} failed.")
    
    else:
        print(f"Results already saved for {run_id}")


if __name__ == "__main__":
    main()
