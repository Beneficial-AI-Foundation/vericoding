"""Success tracking functionality for code2verus"""

import json
from pathlib import Path
import yaml

from code2verus.config import ARTIFACTS


def get_success_base_path(benchmark_name: str, benchmark_path: str = "") -> Path:
    """Get the base path for success tracking, supporting both old and new path structures"""
    # Try to derive path using the same logic as derive_output_path
    if benchmark_path:
        benchmark_path_obj = Path(benchmark_path).resolve()

        # Check if this is a path under benchmarks/lean/
        if (
            "benchmarks" in benchmark_path_obj.parts
            and "lean" in benchmark_path_obj.parts
        ):
            # Find the benchmarks and lean parts in the path
            parts = list(benchmark_path_obj.parts)
            try:
                benchmarks_idx = parts.index("benchmarks")
                lean_idx = parts.index("lean", benchmarks_idx)

                # The benchmark name should be the next part after 'lean'
                if lean_idx + 1 < len(parts):
                    lean_benchmark_name = parts[lean_idx + 1]

                    # Build new path: benchmarks/verus/<lean_benchmark_name>
                    return (
                        Path(*parts[: benchmarks_idx + 1])
                        / "verus"
                        / lean_benchmark_name
                        / "files"
                    )
            except (ValueError, IndexError):
                pass

    # Fallback to current behavior
    return ARTIFACTS / benchmark_name


def load_success_tracking(
    benchmark_name: str, is_flat: bool, benchmark_path: str = ""
) -> dict:
    """Load existing success tracking data"""
    if is_flat:
        base_path = get_success_base_path(benchmark_name, benchmark_path)
        success_file = base_path / "success_tracking.json"
        if success_file.exists():
            try:
                with open(success_file, "r") as f:
                    return json.load(f)
            except Exception:
                pass
    return {}


def save_success_info(
    artifact_path: Path,
    filename: str,
    info: dict,
    benchmark_name: str,
    is_flat: bool,
    benchmark_path: str = "",
):
    """Save success information either as individual YAML or consolidated JSON"""
    if is_flat:
        # Use consolidated JSON file for flat structures
        base_path = get_success_base_path(benchmark_name, benchmark_path)
        success_file = base_path / "success_tracking.json"
        success_file.parent.mkdir(parents=True, exist_ok=True)

        # Load existing data
        existing_data = {}
        if success_file.exists():
            try:
                with open(success_file, "r") as f:
                    existing_data = json.load(f)
            except Exception:
                pass

        # Update with new info
        existing_data[filename] = info

        # Save updated data
        with open(success_file, "w") as f:
            json.dump(existing_data, f, indent=2)
    else:
        # Use individual YAML files for hierarchical structures
        with open(artifact_path / "success.yml", "w") as success_file:
            yaml.dump(info, success_file)


def is_sample_already_successful(
    relative_path: Path,
    benchmark_name: str = "dafnybench",
    filename: str = None,
    is_flat: bool = False,
    benchmark_path: str = "",
) -> bool:
    """Check if a sample already has success: true in its success file"""
    if is_flat and filename:
        # Check consolidated JSON for flat structures
        base_path = get_success_base_path(benchmark_name, benchmark_path)
        success_file = base_path / "success_tracking.json"
        if not success_file.exists():
            return False

        try:
            with open(success_file, "r") as f:
                data = json.load(f)
            return data.get(filename, {}).get("success", False)
        except Exception:
            return False
    else:
        # Check individual YAML files for hierarchical structures
        # Use the new path derivation logic
        if benchmark_path:
            from code2verus.processing import derive_output_path

            base_path = derive_output_path(benchmark_path, benchmark_name, False)
            artifact_path = base_path / relative_path.parent
        else:
            # Fallback to old behavior
            artifact_path = ARTIFACTS / benchmark_name / relative_path.parent

        success_file = artifact_path / "success.yml"

        if not success_file.exists():
            return False

        try:
            with open(success_file, "r") as success_yaml:
                data = yaml.safe_load(success_yaml)
            return data.get("success", False)
        except Exception:
            return False
