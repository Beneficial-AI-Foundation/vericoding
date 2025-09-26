"""Collect and track verification failures with wandb artifacts."""

import hashlib
import json
import time
from pathlib import Path
from typing import Dict, List, Optional, Any
import wandb


class FailureCollector:
    """Collects verification failures and tracks them in wandb."""

    def __init__(self, run_name: Optional[str] = None):
        """Initialize failure collector."""
        self.failures: List[Dict[str, Any]] = []
        self.run_name = run_name or f"analysis_{int(time.time())}"
        self.code_artifacts: Dict[str, str] = {}

    def add_failure(
        self,
        file_path: str,
        iteration: int,
        spec_code: str,
        generated_code: str,
        error_msg: str,
        proof_state: Optional[str] = None,
        metadata: Optional[Dict[str, Any]] = None,
    ):
        """Add a verification failure to the collection."""
        failure_entry = {
            "file": str(Path(file_path).name),
            "file_path": file_path,
            "iteration": iteration,
            "spec_hash": hashlib.md5(spec_code.encode()).hexdigest()[:8],
            "code_hash": hashlib.md5(generated_code.encode()).hexdigest()[:8],
            "error_msg": error_msg,  # Don't truncate error messages
            "proof_state": proof_state or "",
            "timestamp": time.time(),
            "metadata": metadata or {},
        }

        self.failures.append(failure_entry)

        # Store code for artifact creation
        artifact_key = f"{failure_entry['file']}_iter{iteration}"
        self.code_artifacts[artifact_key] = generated_code

    def categorize_error(self, error_msg: str) -> str:
        """Simple heuristic categorization of error messages."""
        error_lower = error_msg.lower()

        if "type mismatch" in error_lower or "has type" in error_lower:
            return "type_mismatch"
        elif "sorry" in error_lower or "incomplete" in error_lower:
            return "incomplete_proof"
        elif "timeout" in error_lower or "timed out" in error_lower:
            return "timeout"
        elif "unknown identifier" in error_lower or "unknown constant" in error_lower:
            return "missing_identifier"
        elif "failed to synthesize" in error_lower:
            return "synthesis_failure"
        elif "tactic failed" in error_lower:
            return "tactic_failure"
        else:
            return "other"

    def log_to_wandb(self):
        """Log collected failures to wandb as table and artifacts."""
        if not wandb.run or not self.failures:
            return

        # Create failures table
        table = wandb.Table(
            columns=[
                "file",
                "iteration",
                "spec_hash",
                "code_hash",
                "error_category",
                "error_msg",
                "proof_state",
                "timestamp",
            ]
        )

        # Add categorized failures to table
        for failure in self.failures:
            error_category = self.categorize_error(failure["error_msg"])
            table.add_data(
                failure["file"],
                failure["iteration"],
                failure["spec_hash"],
                failure["code_hash"],
                error_category,
                failure["error_msg"],
                failure["proof_state"],
                failure["timestamp"],
            )

        # Log table
        wandb.log({"verification_failures": table})

        # Create artifact with all failed code versions
        if self.code_artifacts:
            artifact = wandb.Artifact(
                name=f"failed_code_{self.run_name}",
                type="failed_verification_code",
                metadata={
                    "total_failures": len(self.failures),
                    "unique_files": len(set(f["file"] for f in self.failures)),
                },
            )

            # Add each code version to artifact
            import tempfile

            for key, code in self.code_artifacts.items():
                with tempfile.NamedTemporaryFile(
                    mode="w", suffix=".lean", delete=False
                ) as tmp:
                    tmp.write(code)
                    tmp_path = tmp.name
                artifact.add_file(tmp_path, name=f"{key}.lean")
                Path(tmp_path).unlink(missing_ok=True)

            wandb.log_artifact(artifact)

    def get_failure_summary(self) -> Dict[str, Any]:
        """Get summary statistics of collected failures."""
        if not self.failures:
            return {"total": 0}

        # Categorize all failures
        categories = {}
        for failure in self.failures:
            cat = self.categorize_error(failure["error_msg"])
            categories[cat] = categories.get(cat, 0) + 1

        # Find most problematic files
        file_failures = {}
        for failure in self.failures:
            file_failures[failure["file"]] = file_failures.get(failure["file"], 0) + 1

        most_failures = sorted(file_failures.items(), key=lambda x: x[1], reverse=True)[
            :5
        ]

        return {
            "total_failures": len(self.failures),
            "unique_files": len(set(f["file"] for f in self.failures)),
            "error_categories": categories,
            "most_problematic_files": most_failures,
            "avg_iteration": sum(f["iteration"] for f in self.failures)
            / len(self.failures),
        }

    def save_to_json(self, output_path: Path):
        """Save failures to JSON file for later analysis."""
        data = {
            "run_name": self.run_name,
            "timestamp": time.time(),
            "failures": self.failures,
            "summary": self.get_failure_summary(),
        }

        with open(output_path, "w") as f:
            json.dump(data, f, indent=2)

    @classmethod
    def load_from_json(cls, json_path: Path) -> "FailureCollector":
        """Load failures from JSON file."""
        with open(json_path) as f:
            data = json.load(f)

        collector = cls(run_name=data.get("run_name"))
        collector.failures = data.get("failures", [])

        return collector
