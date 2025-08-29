"""Success tracking functionality for code2verus"""
import json
from pathlib import Path
import yaml

from code2verus.config import ARTIFACTS


def load_success_tracking(benchmark_name: str, is_flat: bool) -> dict:
    """Load existing success tracking data"""
    if is_flat:
        success_file = ARTIFACTS / benchmark_name / "success_tracking.json"
        if success_file.exists():
            try:
                with open(success_file, "r") as f:
                    return json.load(f)
            except Exception:
                pass
    return {}


def save_success_info(artifact_path: Path, filename: str, info: dict, benchmark_name: str, is_flat: bool):
    """Save success information either as individual YAML or consolidated JSON"""
    if is_flat:
        # Use consolidated JSON file for flat structures
        success_file = ARTIFACTS / benchmark_name / "success_tracking.json"
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


def is_sample_already_successful(relative_path: Path, benchmark_name: str = "dafnybench", filename: str = None, is_flat: bool = False) -> bool:
    """Check if a sample already has success: true in its success file"""
    if is_flat and filename:
        # Check consolidated JSON for flat structures
        success_file = ARTIFACTS / benchmark_name / "success_tracking.json"
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
