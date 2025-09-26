#!/usr/bin/env python3
"""
Generate quality analysis metadata for benchmark JSONL files.

This script analyzes benchmark directories and generates TWO types of quality analysis:

1. **BENCHMARK-LEVEL METADATA**: Separate .metadata.json files with overall quality metrics
2. **PER-ENTRY SCORING**: Enhanced JSONL files with individual quality scores for each entry

DUAL OUTPUT STRUCTURE:
    benchmarks/verus/humaneval/
    ├── verus_humaneval.jsonl                    # Original entries (unchanged)
    ├── verus_humaneval.metadata.json            # Benchmark-level metadata
    ├── verus_humaneval_with_entry_qa.jsonl      # Enhanced with per-entry scores
    └── yaml/, files/                            # Source files

SCORING METHODOLOGY:
Uses normalized scoring for cross-benchmark comparison where quality issues are
weighted by relative importance (weights sum to 1.0).

**BENCHMARK-LEVEL FORMULA (NORMALIZED):**
    final_score = 100 × (1 - penalty_fraction)  [0-100 scale, comparable across benchmarks]
    penalty_fraction = Σ(weight_i × proportion_i)
    proportion_i = issue_count_i / total_entries

**EXAMPLE SCORES:**
    - 100: Perfect quality (no issues)
    - 80: Good quality (20% penalty from issues)
    - 50: Moderate quality (50% penalty from issues)
    - 0: Poor quality (all entries have critical issues)

**PER-ENTRY FORMULA:**
    individual_score = 1 - Σ(weight_i × p_i)  [0-1 scale per entry]
    p_i = 1 if entry has issue_i, else 0 (binary penalty per entry)

QUALITY FACTORS ANALYZED:
- **Verus**: specs with defaults (30%), exec bodies (50%), ghost types (5%), near-duplicates (15%)
- **Dafny**: func defaults (40%), method bodies (45%), near-duplicates (15%)
- **Lean**: sorry usage (85%), near-duplicates (15%)
- **All languages**: Vector similarity analysis for near-duplicate detection

EXAMPLE PER-ENTRY OUTPUT:
    {
      "id": "VH0000",
      "source_id": "humaneval_000",
      ... (original entry data) ...
      "qa_entry_metadata": {
        "issues": {
          "specs_with_default_values": 1,
          "execs_with_bodies": 0,
          "execs_with_ghost_types": 0,
          "near_duplicates": 1
        },
        "individual_score": 0.55  // 1 - (0.30×1 + 0.15×1) = 0.55
      }
    }

DEPENDENCIES:
- Required for near-duplicate detection: sentence-transformers, scikit-learn, faiss-cpu
- Install with: uv add sentence-transformers scikit-learn faiss-cpu

Usage:
    # Command line usage - generates/overwrites metadata files AND enhanced JSONL
    python3 add_qa_metadata.py benchmarks                    # Process all benchmarks
    python3 add_qa_metadata.py benchmarks/verus/apps        # Process specific benchmark
    python3 add_qa_metadata.py --config custom_config.yaml  # Use custom configuration
    python3 add_qa_metadata.py --output-metadata summary benchmarks  # Show metadata summary

    # Programmatic usage
    from add_qa_metadata import load_benchmark_with_metadata, get_benchmark_quality_score

    # Load entries with metadata
    entries, metadata = load_benchmark_with_metadata("benchmarks/verus/humaneval/verus_humaneval.jsonl")

    # Get benchmark quality score
    score = get_benchmark_quality_score("benchmarks/verus/humaneval/verus_humaneval.jsonl")

    # List all benchmarks with metadata
    from add_qa_metadata import list_benchmarks_with_metadata
    benchmarks = list_benchmarks_with_metadata("benchmarks")
"""

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
import yaml

# Import similarity analysis
try:
    from .optimized_vector_similarity import get_near_duplicates_for_benchmark
except ImportError:
    # Fallback for when run as script
    import sys
    import os

    sys.path.append(os.path.dirname(__file__))
    from optimized_vector_similarity import get_near_duplicates_for_benchmark


class QAMetadataGenerator:
    def __init__(
        self,
        quiet: bool = False,
        config_path: Optional[Path] = None,
        metadata_only: bool = False,
    ):
        self.quiet = quiet
        self.metadata_only = metadata_only
        self.script_dir = Path(__file__).parent
        self.config = self.load_config(config_path)

    def load_config(self, config_path: Optional[Path] = None) -> Dict[str, Any]:
        """Load configuration from YAML file."""
        if config_path is None:
            config_path = self.script_dir / "config" / "qa_config.yaml"

        try:
            with open(config_path, "r", encoding="utf-8") as f:
                config = yaml.safe_load(f)
                self.log(f"Loaded configuration from {config_path}")
                return config
        except Exception as e:
            self.log(f"Warning: Could not load config from {config_path}: {e}")
            self.log("Using default configuration values")
            return self.get_default_config()

    def get_default_config(self) -> Dict[str, Any]:
        """Get default configuration values."""
        return {
            "similarity": {
                "method": "optimized_vector",
                "threshold": 0.85,
                "embedding_focus": "semantic",
                "embedding_model": "all-MiniLM-L6-v2",
                "max_examples": 5,
                "cache_dir": ".vector_cache",
                "batch_size": 32,
                "use_gpu": False,
            },
            "scoring": {
                "base_score_mode": "proportional",
                "fixed_base_score": 100,
                "proportional_points_per_entry": 0.5,
                "proportional_max_score": 500,
                "proportional_min_score": 50,
                "logarithmic_multiplier": 50,
                "verus": {
                    "specs_with_default_values_penalty": 5,
                    "execs_with_bodies_penalty": 12,
                    "execs_with_ghost_types_penalty": 0.5,
                    "near_duplicates_penalty": 2,
                },
                "dafny": {
                    "functions_with_default_values_penalty": 5,
                    "methods_with_bodies_penalty": 12,
                    "near_duplicates_penalty": 2,
                },
                "lean": {
                    "definitions_with_sorry_penalty": 12,
                    "near_duplicates_penalty": 2,
                },
            },
            "qa_scripts": {
                "script_timeout": 300,
                "include_problematic_dirs": False,
                "output_format": "json",
            },
        }

    def log(self, message: str):
        """Log message if not in quiet mode."""
        if not self.quiet:
            print(message)

    def detect_language(self, benchmark_path: Path) -> Optional[str]:
        """Detect language from benchmark path structure."""
        parts = benchmark_path.parts

        # Look for language in path: benchmarks/<language>/<benchmark_name>
        for i, part in enumerate(parts):
            if part == "benchmarks" and i + 1 < len(parts):
                potential_lang = parts[i + 1]
                if potential_lang in ["verus", "dafny", "lean"]:
                    return potential_lang

        # Fallback: check for language-specific files
        if any(benchmark_path.glob("**/*.rs")) or any(
            benchmark_path.glob("**/*verus*")
        ):
            return "verus"
        elif any(benchmark_path.glob("**/*.dfy")) or any(
            benchmark_path.glob("**/*dafny*")
        ):
            return "dafny"
        elif any(benchmark_path.glob("**/*.lean")) or any(
            benchmark_path.glob("**/*lean*")
        ):
            return "lean"

        return None

    def find_jsonl_files(self, benchmark_path: Path) -> List[Path]:
        """Find original JSONL files in benchmark directory (excluding processed files)."""
        jsonl_files = list(benchmark_path.glob("*.jsonl"))

        # Filter out files that are processed versions
        # We want to process only the original base files
        original_files = [
            f
            for f in jsonl_files
            if not f.name.endswith("_with_qa_metadata.jsonl")
            and not f.name.endswith("_with_entry_qa.jsonl")
        ]

        if not original_files:
            self.log(f"No original JSONL files found in {benchmark_path}")

        return original_files

    def run_qa_script(
        self, script_name: str, benchmark_path: Path, extra_args: List[str] = None
    ) -> Dict[str, Any]:
        """Run a quality analysis script and return structured results."""
        script_path = self.script_dir / script_name
        if not script_path.exists():
            raise FileNotFoundError(f"QA script not found: {script_path}")

        cmd = [
            sys.executable,
            str(script_path),
            str(benchmark_path),
            "--output",
            "json",
            "--quiet",
        ]
        if extra_args:
            cmd.extend(extra_args)

        try:
            result = subprocess.run(cmd, capture_output=True, text=True, check=False)

            if result.stdout.strip():
                try:
                    return json.loads(result.stdout)
                except json.JSONDecodeError as e:
                    self.log(f"Warning: Could not parse JSON output from {script_name}")
                    self.log(f"  JSON error: {e}")
                    self.log(f"  Raw output: {result.stdout[:200]}...")
                    if result.stderr:
                        self.log(f"  Stderr: {result.stderr[:200]}...")
                    return {}
            else:
                return {}

        except Exception as e:
            self.log(f"Error running {script_name}: {e}")
            return {}

    def extract_file_lists_from_qa_output(
        self, qa_output: Dict[str, Any]
    ) -> Dict[str, List[str]]:
        """Extract file lists from QA script output."""
        file_lists = {}

        # Handle different QA script output formats
        if "issues" in qa_output:
            # Type checker format (check_verus_types.py)
            files_with_issues = list(
                set(
                    issue.get("file", "")
                    for issue in qa_output["issues"]
                    if issue.get("file")
                )
            )
            file_lists["files_with_issues"] = files_with_issues

        # Look for common patterns in QA output
        for key, value in qa_output.items():
            if isinstance(value, list) and key.startswith("files_"):
                file_lists[key] = value

        return file_lists

    def generate_similarity_metadata(self, benchmark_path: Path) -> Dict[str, Any]:
        """Generate similarity metadata for near duplicates."""
        try:
            # Look for YAML files in the benchmark
            yaml_dir = benchmark_path / "yaml"
            if not yaml_dir.exists():
                yaml_dir = benchmark_path  # Fallback to benchmark root

            sim_config = self.config["similarity"]
            similarity_data = get_near_duplicates_for_benchmark(
                str(yaml_dir),
                similarity_threshold=sim_config["threshold"],
                embedding_focus=sim_config["embedding_focus"],
                embedding_model=sim_config.get("embedding_model", "all-MiniLM-L6-v2"),
                cache_dir=sim_config["cache_dir"],
                batch_size=sim_config["batch_size"],
                use_gpu=sim_config.get("use_gpu", False),
                max_examples=sim_config["max_examples"],
            )

            return similarity_data

        except ImportError as e:
            # Re-raise ImportError with clear context about what's missing
            raise ImportError(
                f"Similarity analysis dependencies missing: {e}\n"
                f"This is required for near-duplicate detection in quality analysis.\n"
                f"Install with: uv add sentence-transformers scikit-learn faiss-cpu"
            ) from e
        except Exception as e:
            self.log(f"Warning: Could not generate similarity metadata: {e}")
            return {"examples": [], "total_count": 0}

    def generate_verus_metadata(self, benchmark_path: Path) -> Dict[str, Any]:
        """Generate QA metadata for Verus benchmarks."""
        metadata = {
            "specs_with_default_values": [],
            "execs_with_bodies": [],
            "execs_with_ghost_types": [],
            "score": 100,
        }

        try:
            # Only analyze the yaml directory, not poor/non_compiling directories
            yaml_dir = benchmark_path / "yaml"
            if yaml_dir.exists():
                analysis_path = yaml_dir
                self.log(f"Analyzing yaml directory: {yaml_dir}")
            else:
                analysis_path = benchmark_path
                self.log(
                    f"No yaml directory found, analyzing entire benchmark: {benchmark_path}"
                )

            # 1. Check spec functions for default values
            spec_output = self.run_qa_script(
                "verus/check_spec_functions.py", analysis_path
            )
            spec_files = self.extract_file_lists_from_qa_output(spec_output)
            metadata["specs_with_default_values"] = spec_files.get(
                "files_with_defaults", []
            )

            # 2. Check executable functions for implementations
            func_output = self.run_qa_script(
                "verus/check_verus_functions.py", analysis_path
            )
            func_files = self.extract_file_lists_from_qa_output(func_output)
            metadata["execs_with_bodies"] = func_files.get(
                "files_with_implementations", []
            )

            # 3. Check for ghost types in executable functions
            type_output = self.run_qa_script(
                "verus/check_verus_types.py", analysis_path
            )
            type_files = self.extract_file_lists_from_qa_output(type_output)
            metadata["execs_with_ghost_types"] = type_files.get("files_with_issues", [])

            # Add similarity analysis
            similarity_data = self.generate_similarity_metadata(benchmark_path)
            metadata["near_duplicates"] = similarity_data

            # Calculate score using normalized weights approach
            base_score = self.get_base_score_for_benchmark(benchmark_path)
            metadata["base_score"] = base_score

            # Get entry count for normalization
            jsonl_files = list(benchmark_path.glob("*.jsonl"))
            entry_count = 1  # Fallback
            if jsonl_files:
                try:
                    with open(jsonl_files[0], "r", encoding="utf-8") as f:
                        entry_count = sum(1 for line in f if line.strip())
                except Exception:
                    entry_count = 1

            # Prepare issue counts and weights for normalized scoring
            issue_counts = {
                "specs_with_default_values": len(metadata["specs_with_default_values"]),
                "execs_with_bodies": len(metadata["execs_with_bodies"]),
                "execs_with_ghost_types": len(metadata["execs_with_ghost_types"]),
                "near_duplicates": similarity_data["total_count"],
            }

            scoring_config = self.config["scoring"]
            weights = scoring_config["verus"]["weights"]

            # Calculate normalized score
            metadata["score"] = self.calculate_normalized_score(
                base_score, issue_counts, weights, entry_count
            )

        except Exception as e:
            self.log(f"Error generating Verus metadata: {e}")

        return metadata

    def generate_dafny_metadata(self, benchmark_path: Path) -> Dict[str, Any]:
        """Generate QA metadata for Dafny benchmarks."""
        metadata = {
            "functions_with_default_values": [],
            "methods_with_bodies": [],
            "score": 100,
        }

        try:
            # Only analyze the yaml directory, not poor/non_compiling directories
            yaml_dir = benchmark_path / "yaml"
            analysis_path = yaml_dir if yaml_dir.exists() else benchmark_path

            # 1. Check functions/predicates for default values
            func_output = self.run_qa_script(
                "dafny/check_dafny_functions.py", analysis_path
            )
            func_files = self.extract_file_lists_from_qa_output(func_output)
            metadata["functions_with_default_values"] = func_files.get(
                "files_with_defaults", []
            )

            # 2. Check methods for implementations
            method_output = self.run_qa_script(
                "dafny/check_dafny_methods.py", analysis_path
            )
            method_files = self.extract_file_lists_from_qa_output(method_output)
            metadata["methods_with_bodies"] = method_files.get(
                "files_with_implementations", []
            )

            # Add similarity analysis
            similarity_data = self.generate_similarity_metadata(benchmark_path)
            metadata["near_duplicates"] = similarity_data

            # Calculate score using normalized weights approach
            base_score = self.get_base_score_for_benchmark(benchmark_path)
            metadata["base_score"] = base_score

            # Get entry count for normalization
            jsonl_files = list(benchmark_path.glob("*.jsonl"))
            entry_count = 1  # Fallback
            if jsonl_files:
                try:
                    with open(jsonl_files[0], "r", encoding="utf-8") as f:
                        entry_count = sum(1 for line in f if line.strip())
                except Exception:
                    entry_count = 1

            # Prepare issue counts and weights for normalized scoring
            issue_counts = {
                "functions_with_default_values": len(
                    metadata["functions_with_default_values"]
                ),
                "methods_with_bodies": len(metadata["methods_with_bodies"]),
                "near_duplicates": similarity_data["total_count"],
            }

            scoring_config = self.config["scoring"]
            weights = scoring_config["dafny"]["weights"]

            # Calculate normalized score
            metadata["score"] = self.calculate_normalized_score(
                base_score, issue_counts, weights, entry_count
            )

        except Exception as e:
            self.log(f"Error generating Dafny metadata: {e}")

        return metadata

    def generate_lean_metadata(self, benchmark_path: Path) -> Dict[str, Any]:
        """Generate QA metadata for Lean benchmarks."""
        metadata = {"definitions_with_sorry": [], "score": 100}

        try:
            # Only analyze the yaml directory, not poor/non_compiling directories
            yaml_dir = benchmark_path / "yaml"
            analysis_path = yaml_dir if yaml_dir.exists() else benchmark_path

            # Check definitions for sorry usage
            lean_output = self.run_qa_script(
                "lean/check_lean_definitions.py", analysis_path
            )
            lean_files = self.extract_file_lists_from_qa_output(lean_output)
            metadata["definitions_with_sorry"] = lean_files.get("files_with_sorry", [])

            # Add similarity analysis
            similarity_data = self.generate_similarity_metadata(benchmark_path)
            metadata["near_duplicates"] = similarity_data

            # Calculate score using normalized weights approach
            base_score = self.get_base_score_for_benchmark(benchmark_path)
            metadata["base_score"] = base_score

            # Get entry count for normalization
            jsonl_files = list(benchmark_path.glob("*.jsonl"))
            entry_count = 1  # Fallback
            if jsonl_files:
                try:
                    with open(jsonl_files[0], "r", encoding="utf-8") as f:
                        entry_count = sum(1 for line in f if line.strip())
                except Exception:
                    entry_count = 1

            # Prepare issue counts and weights for normalized scoring
            issue_counts = {
                "definitions_with_sorry": len(metadata["definitions_with_sorry"]),
                "near_duplicates": similarity_data["total_count"],
            }

            scoring_config = self.config["scoring"]
            weights = scoring_config["lean"]["weights"]

            # Calculate normalized score
            metadata["score"] = self.calculate_normalized_score(
                base_score, issue_counts, weights, entry_count
            )

        except Exception as e:
            self.log(f"Error generating Lean metadata: {e}")

        return metadata

    def calculate_base_score(self, jsonl_path: Path) -> int:
        """Calculate base score based on configuration and JSONL entry count."""
        try:
            # Count entries in JSONL file
            with open(jsonl_path, "r", encoding="utf-8") as f:
                entry_count = sum(1 for line in f if line.strip())

            scoring_config = self.config["scoring"]
            mode = scoring_config.get("base_score_mode", "fixed")

            if mode == "fixed":
                return scoring_config.get("fixed_base_score", 100)

            elif mode == "proportional":
                points_per_entry = scoring_config.get(
                    "proportional_points_per_entry", 0.5
                )
                max_score = scoring_config.get("proportional_max_score", 500)
                min_score = scoring_config.get("proportional_min_score", 50)

                calculated_score = entry_count * points_per_entry
                return int(max(min_score, min(max_score, calculated_score)))

            elif mode == "logarithmic":
                import math

                multiplier = scoring_config.get("logarithmic_multiplier", 50)
                return int(multiplier * math.log(entry_count + 1))

            else:
                self.log(
                    f"Warning: Unknown base_score_mode '{mode}', using fixed score"
                )
                return scoring_config.get("fixed_base_score", 100)

        except Exception as e:
            self.log(f"Error calculating base score: {e}")
            return 100  # Fallback to default

    def get_base_score_for_benchmark(self, benchmark_path: Path) -> int:
        """Get the base score for a benchmark by finding its JSONL file."""
        try:
            # Find the JSONL file to calculate base score
            jsonl_files = list(benchmark_path.glob("*.jsonl"))
            if jsonl_files:
                return self.calculate_base_score(jsonl_files[0])
            else:
                # Fallback to fixed base score if no JSONL file found
                scoring_config = self.config["scoring"]
                return scoring_config.get("fixed_base_score", 100)
        except Exception as e:
            self.log(f"Error getting base score for benchmark: {e}")
            return 100  # Fallback to default

    def calculate_normalized_score(
        self,
        base_score: int,
        issue_counts: Dict[str, int],
        weights: Dict[str, float],
        entry_count: int,
    ) -> float:
        """
        Calculate quality score using normalized per-entry approach for cross-benchmark comparison.

        Two scoring modes:
        1. Original: final_score = base_score × (1 - penalty_fraction) [size-dependent]
        2. Normalized: final_score = 100 × (1 - penalty_fraction) [size-independent]

        Where: penalty_fraction = Σ(weight_i × proportion_i)
               proportion_i = count_i / total_entries

        Args:
            base_score: Base score from dataset size (used in original mode)
            issue_counts: Dictionary mapping issue types to counts
            weights: Dictionary mapping issue types to normalized weights (sum to 1.0)
            entry_count: Number of entries in benchmark

        Returns:
            Final quality score - normalized for cross-benchmark comparison
        """
        try:
            # Calculate penalty fraction using direct proportions
            penalty_fraction = 0.0

            # Avoid division by zero
            if entry_count == 0:
                return 100.0  # Perfect score for empty benchmarks

            for issue_type, count in issue_counts.items():
                if count == 0:
                    continue

                # Find corresponding weight
                weight_key = f"{issue_type}_weight"

                if weight_key in weights:
                    weight = weights[weight_key]
                    proportion = count / entry_count
                    penalty_fraction += weight * proportion

            # Use normalized scoring mode for cross-benchmark comparison
            # Score represents average quality per entry on 0-100 scale
            scoring_config = self.config["scoring"]
            use_normalized = scoring_config.get("use_normalized_quality", True)

            if use_normalized:
                # Normalized mode: 100 × (1 - penalty_fraction)
                # This gives comparable scores across benchmarks of any size
                final_score = 100.0 * (1.0 - penalty_fraction)
            else:
                # Original mode: base_score × (1 - penalty_fraction)
                # This preserves the old behavior where larger benchmarks get higher scores
                final_score = base_score * (1.0 - penalty_fraction)

            # Ensure score doesn't go negative (safety check)
            final_score = max(0.0, final_score)

            return final_score

        except Exception as e:
            self.log(f"Error calculating normalized score: {e}")
            # Fallback to simple base score
            return float(base_score)

    def analyze_single_entry(
        self,
        entry: Dict,
        benchmark_path: Path,
        language: str,
        near_duplicate_files: set = None,
    ) -> Dict[str, Any]:
        """Analyze a single JSONL entry for quality issues."""
        source_id = entry.get("source_id", "")

        # Find the corresponding files
        yaml_file = benchmark_path / "yaml" / f"{source_id}.yaml"
        files_dir = benchmark_path / "files"

        # Find the actual source file based on language
        if language == "lean":
            source_file = files_dir / f"{source_id}.lean"
        elif language == "verus":
            source_file = files_dir / f"{source_id}.rs"
        elif language == "dafny":
            source_file = files_dir / f"{source_id}.dfy"
        else:
            source_file = None

        # Initialize entry metadata
        entry_qa = {"issues": {}, "individual_score": 1.0}

        # Find files to analyze for this entry
        files_to_check = []
        if yaml_file.exists():
            files_to_check.append(("yaml", str(yaml_file)))
        if source_file and source_file.exists():
            files_to_check.append(("source", str(source_file)))

        # Analyze files based on language
        if language == "lean":
            entry_qa["issues"] = self.analyze_lean_entry_files(files_to_check)
        elif language == "verus":
            entry_qa["issues"] = self.analyze_verus_entry_files(files_to_check)
        elif language == "dafny":
            entry_qa["issues"] = self.analyze_dafny_entry_files(files_to_check)

        # Add near-duplicate analysis for this entry
        entry_qa["issues"]["near_duplicates"] = self.check_entry_for_near_duplicates(
            entry, benchmark_path, near_duplicate_files
        )

        # Calculate individual score using the same formula as benchmark-level
        # but with per-entry issue counts
        weights = self.config["scoring"][language]["weights"]
        entry_qa["individual_score"] = self.calculate_entry_score(
            entry_qa["issues"], weights
        )

        return entry_qa

    def calculate_entry_score(
        self, issues: Dict[str, int], weights: Dict[str, float]
    ) -> float:
        """Calculate quality score for a single entry using 1 - Σ(weight_i × p_i) formula."""
        penalty = 0.0

        for issue_type, count in issues.items():
            weight_key = f"{issue_type}_weight"
            if weight_key in weights and count > 0:
                # For individual entries, p_i is simply the count (since it's per-entry)
                # We can scale this or normalize it based on the specific issue type
                weight = weights[weight_key]

                # For binary issues (has issue or not), p_i = 1 if issue exists
                # For count-based issues, we could use the actual count
                p_i = min(1.0, count)  # Cap at 1.0 for now (binary approach)
                penalty += weight * p_i

        # Ensure score doesn't go below 0
        return max(0.0, 1.0 - penalty)

    def analyze_lean_entry_files(
        self, files_to_check: List[Tuple[str, str]]
    ) -> Dict[str, int]:
        """Analyze Lean files for a single entry."""
        issues = {
            "definitions_with_sorry": 0,
            "near_duplicates": 0,  # Will be filled by caller
        }

        for file_type, file_path in files_to_check:
            # Use our existing QA script to analyze the file
            try:
                if file_path.endswith(".lean"):
                    result = self.run_qa_script(
                        "lean/check_lean_definitions.py", Path(file_path)
                    )
                    # Parse the result to count issues
                    if isinstance(result, dict) and "files_with_sorry" in result:
                        if file_path in result.get("files_with_sorry", []):
                            issues["definitions_with_sorry"] += 1
                elif file_path.endswith(".yaml"):
                    # For YAML files, extract and analyze content
                    issues["definitions_with_sorry"] += self.count_sorry_in_yaml(
                        file_path
                    )
            except Exception as e:
                self.log(f"Warning: Could not analyze {file_path}: {e}")

        return issues

    def analyze_verus_entry_files(
        self, files_to_check: List[Tuple[str, str]]
    ) -> Dict[str, int]:
        """Analyze Verus files for a single entry."""
        issues = {
            "specs_with_default_values": 0,
            "execs_with_bodies": 0,
            "execs_with_ghost_types": 0,
            "near_duplicates": 0,  # Will be filled by caller
        }

        for file_type, file_path in files_to_check:
            try:
                if file_path.endswith(".rs"):
                    # Check for implementations in exec functions
                    result = self.run_qa_script(
                        "verus/check_verus_functions.py", Path(file_path)
                    )
                    if (
                        isinstance(result, dict)
                        and "files_with_implementations" in result
                    ):
                        if file_path in result.get("files_with_implementations", []):
                            issues["execs_with_bodies"] += 1

                    # Check for ghost types
                    result = self.run_qa_script(
                        "verus/check_verus_types.py", Path(file_path)
                    )
                    if isinstance(result, dict) and "files_with_issues" in result:
                        if file_path in result.get("files_with_issues", []):
                            issues["execs_with_ghost_types"] += 1

                elif file_path.endswith(".yaml"):
                    # Check spec functions in YAML
                    result = self.run_qa_script(
                        "verus/check_spec_functions.py", Path(file_path)
                    )
                    if isinstance(result, dict) and "files_with_defaults" in result:
                        if file_path in result.get("files_with_defaults", []):
                            issues["specs_with_default_values"] += 1
            except Exception as e:
                self.log(f"Warning: Could not analyze {file_path}: {e}")

        return issues

    def analyze_dafny_entry_files(
        self, files_to_check: List[Tuple[str, str]]
    ) -> Dict[str, int]:
        """Analyze Dafny files for a single entry."""
        issues = {
            "functions_with_default_values": 0,
            "methods_with_bodies": 0,
            "near_duplicates": 0,  # Will be filled by caller
        }

        for file_type, file_path in files_to_check:
            try:
                if file_path.endswith(".yaml"):
                    # Both functions and methods are analyzed from YAML files
                    # Check functions in YAML
                    func_result = self.run_qa_script(
                        "dafny/check_dafny_functions.py", Path(file_path)
                    )
                    if (
                        isinstance(func_result, dict)
                        and "files_with_defaults" in func_result
                    ):
                        if file_path in func_result.get("files_with_defaults", []):
                            issues["functions_with_default_values"] += 1

                    # Check methods in YAML
                    method_result = self.run_qa_script(
                        "dafny/check_dafny_methods.py", Path(file_path)
                    )
                    if (
                        isinstance(method_result, dict)
                        and "files_with_implementations" in method_result
                    ):
                        if file_path in method_result.get(
                            "files_with_implementations", []
                        ):
                            issues["methods_with_bodies"] += 1

                # Skip .dfy files - they don't contain the spec information we need
                # The YAML files contain the specifications we're analyzing

            except Exception as e:
                self.log(f"Warning: Could not analyze {file_path}: {e}")

        return issues

    def count_sorry_in_yaml(self, yaml_path: str) -> int:
        """Count sorry occurrences in YAML file content."""
        try:
            with open(yaml_path, "r", encoding="utf-8") as f:
                content = f.read()

            # Look for sorry in various sections
            sorry_count = 0
            sections = ["vc-definitions", "vc-theorems", "vc-preamble"]

            for section in sections:
                section_match = re.search(
                    rf"{section}:\s*(?:\|-?\s*\n)?(.*?)(?=\n\w+:|$)", content, re.DOTALL
                )
                if section_match:
                    section_content = section_match.group(1)
                    # Count occurrences of sorry (as standalone word)
                    sorry_matches = re.findall(r"\bsorry\b", section_content)
                    sorry_count += len(sorry_matches)

            return 1 if sorry_count > 0 else 0  # Binary: has sorry or not
        except Exception as e:
            self.log(f"Warning: Could not analyze YAML {yaml_path}: {e}")
            return 0

    def extract_near_duplicate_files(self, similarity_data: Dict[str, Any]) -> set:
        """Extract set of files that are identified as near-duplicates."""
        near_duplicate_files = set()

        if "examples" in similarity_data:
            for example in similarity_data["examples"]:
                # Add all files in each duplicate group
                if "files" in example:
                    for file_path in example["files"]:
                        # Extract just the filename from the path
                        filename = Path(file_path).name
                        near_duplicate_files.add(filename)

        return near_duplicate_files

    def check_entry_for_near_duplicates(
        self, entry: Dict, benchmark_path: Path, near_duplicate_files: set = None
    ) -> int:
        """Check if this entry's files are identified as near-duplicates."""
        if near_duplicate_files is None:
            return 0

        source_id = entry.get("source_id", "")

        # Check if this entry's YAML file is in the near-duplicates set
        yaml_filename = f"{source_id}.yaml"

        if yaml_filename in near_duplicate_files:
            return 1

        return 0

    def create_metadata_file(
        self, jsonl_path: Path, benchmark_path: Path, language: str
    ) -> Tuple[bool, Optional[Dict]]:
        """Create a separate metadata file for the benchmark."""
        metadata_path = jsonl_path.parent / f"{jsonl_path.stem}.metadata.json"

        self.log(f"Generating metadata for {jsonl_path.name} -> {metadata_path.name}")

        try:
            # Generate language-specific metadata
            if language == "verus":
                qa_metadata = self.generate_verus_metadata(benchmark_path)
            elif language == "dafny":
                qa_metadata = self.generate_dafny_metadata(benchmark_path)
            elif language == "lean":
                qa_metadata = self.generate_lean_metadata(benchmark_path)
            else:
                self.log(f"Unsupported language: {language}")
                return False, None

            # Count entries in JSONL file
            entry_count = 0
            try:
                with open(jsonl_path, "r", encoding="utf-8") as f:
                    entry_count = sum(1 for line in f if line.strip())
            except Exception as e:
                self.log(f"Warning: Could not count entries in {jsonl_path}: {e}")
                entry_count = 0

            # Create comprehensive metadata structure
            metadata = {
                "benchmark_info": {
                    "name": jsonl_path.stem,
                    "language": language,
                    "source": qa_metadata.get("source", "unknown"),
                    "entry_count": entry_count,
                    "benchmark_path": str(benchmark_path),
                },
                "qa_metadata": qa_metadata,
                "generated_at": datetime.now().isoformat(),
                "config_version": "2.0",
                "format_version": "separate_metadata_v1",
            }

            # Write metadata file
            with open(metadata_path, "w", encoding="utf-8") as f:
                json.dump(metadata, f, indent=2, ensure_ascii=False)

            self.log(f"✅ Created {metadata_path}")
            return True, qa_metadata

        except Exception as e:
            self.log(f"❌ Error creating metadata file: {e}")
            return False, None

    def create_enhanced_jsonl_file(
        self, jsonl_path: Path, benchmark_path: Path, language: str
    ) -> Tuple[bool, Optional[Dict]]:
        """Create enhanced JSONL file with per-entry QA metadata."""
        enhanced_path = jsonl_path.parent / f"{jsonl_path.stem}_with_entry_qa.jsonl"

        self.log(f"Creating enhanced JSONL: {jsonl_path.name} -> {enhanced_path.name}")

        # Pre-compute near-duplicates for the entire benchmark
        self.log("Computing near-duplicates for benchmark...")
        similarity_data = self.generate_similarity_metadata(benchmark_path)
        near_duplicate_files = self.extract_near_duplicate_files(similarity_data)
        self.log(f"Found {len(near_duplicate_files)} near-duplicate files")

        try:
            entries_processed = 0
            with (
                open(jsonl_path, "r", encoding="utf-8") as infile,
                open(enhanced_path, "w", encoding="utf-8") as outfile,
            ):
                for line_num, line in enumerate(infile, 1):
                    line = line.strip()
                    if not line:
                        continue

                    try:
                        entry = json.loads(line)

                        # Analyze this specific entry
                        entry_qa = self.analyze_single_entry(
                            entry, benchmark_path, language, near_duplicate_files
                        )

                        # Add per-entry QA metadata
                        entry["qa_entry_metadata"] = entry_qa

                        # Write enhanced entry
                        outfile.write(json.dumps(entry, ensure_ascii=False) + "\n")
                        entries_processed += 1

                        # Log progress for large files
                        if entries_processed % 100 == 0:
                            self.log(f"  Processed {entries_processed} entries...")

                    except json.JSONDecodeError as e:
                        self.log(
                            f"Warning: Could not parse line {line_num} in {jsonl_path}: {e}"
                        )
                        continue

            self.log(
                f"✅ Created enhanced JSONL with {entries_processed} entries: {enhanced_path}"
            )

            return True, {"entries_processed": entries_processed}

        except Exception as e:
            self.log(f"❌ Error creating enhanced JSONL file: {e}")
            return False, None

    def process_benchmark(self, benchmark_path: Path) -> Tuple[bool, Optional[Dict]]:
        """Process a single benchmark directory."""
        if not benchmark_path.exists():
            self.log(f"Error: Benchmark path does not exist: {benchmark_path}")
            return False, None

        if not benchmark_path.is_dir():
            self.log(f"Error: Path is not a directory: {benchmark_path}")
            return False, None

        # Detect language
        language = self.detect_language(benchmark_path)
        if not language:
            self.log(f"Warning: Could not detect language for {benchmark_path}")
            return False, None

        self.log(f"Processing {benchmark_path} (detected language: {language})")

        # Find JSONL files
        jsonl_files = self.find_jsonl_files(benchmark_path)
        if not jsonl_files:
            return False, None

        # Create benchmark metadata and optionally enhanced JSONL files
        success_count = 0
        qa_metadata = None
        for jsonl_file in jsonl_files:
            # Create benchmark-level metadata file
            success_meta, metadata = self.create_metadata_file(
                jsonl_file, benchmark_path, language
            )

            # Conditionally create enhanced JSONL with per-entry QA metadata
            success_jsonl = True  # Default to success if skipping
            if not self.metadata_only:
                success_jsonl, _ = self.create_enhanced_jsonl_file(
                    jsonl_file, benchmark_path, language
                )

            if success_meta and success_jsonl:
                success_count += 1
                qa_metadata = (
                    metadata  # Store the metadata (same for all files in benchmark)
                )

        operation_desc = (
            "metadata only" if self.metadata_only else "metadata and enhanced JSONL"
        )
        self.log(
            f"Created {operation_desc} for {success_count}/{len(jsonl_files)} files in {benchmark_path}"
        )
        return success_count > 0, qa_metadata

    def process_benchmarks_directory(
        self, benchmarks_root: Path
    ) -> Tuple[bool, Dict[str, Dict]]:
        """Process all benchmarks in a directory."""
        all_metadata = {}

        if not benchmarks_root.exists():
            self.log(f"Error: Benchmarks directory does not exist: {benchmarks_root}")
            return False, all_metadata

        # Check if this is a single benchmark or benchmarks root
        # Special case: if this is the root "benchmarks" directory, skip the JSONL check
        # and proceed to process subdirectories
        if benchmarks_root.name != "benchmarks":
            jsonl_files = self.find_jsonl_files(benchmarks_root)
            if jsonl_files:
                # This directory contains JSONL files, treat as single benchmark
                success, metadata = self.process_benchmark(benchmarks_root)
                if success and metadata:
                    all_metadata[str(benchmarks_root)] = metadata
                return success, all_metadata

        # Handle different input patterns:
        # 1. benchmarks/verus -> process all benchmarks in verus language
        # 2. benchmarks -> process all benchmarks in all languages
        benchmark_dirs = []

        # Check if this is a language directory (benchmarks/verus, benchmarks/dafny, benchmarks/lean)
        if (
            benchmarks_root.name in ["verus", "dafny", "lean"]
            and benchmarks_root.parent.name == "benchmarks"
        ):
            # This is a language directory, find all benchmark subdirectories within it
            for bench_dir in benchmarks_root.iterdir():
                if bench_dir.is_dir() and self.find_jsonl_files(bench_dir):
                    benchmark_dirs.append(bench_dir)
        else:
            # This is a benchmarks root, find all benchmark subdirectories in all languages
            for lang_dir in benchmarks_root.iterdir():
                if lang_dir.is_dir() and lang_dir.name in ["verus", "dafny", "lean"]:
                    for bench_dir in lang_dir.iterdir():
                        if bench_dir.is_dir() and self.find_jsonl_files(bench_dir):
                            benchmark_dirs.append(bench_dir)

        if not benchmark_dirs:
            self.log(
                f"No benchmark directories with JSONL files found in {benchmarks_root}"
            )
            return False, all_metadata

        self.log(f"Found {len(benchmark_dirs)} benchmark directories")

        # Process each benchmark
        success_count = 0
        for bench_dir in benchmark_dirs:
            success, metadata = self.process_benchmark(bench_dir)
            if success:
                success_count += 1
                if metadata:
                    all_metadata[str(bench_dir)] = metadata

        self.log(
            f"\n🎉 Successfully processed {success_count}/{len(benchmark_dirs)} benchmarks"
        )
        return success_count > 0, all_metadata

    def get_metadata_only(self, benchmark_path: Path) -> Optional[Dict]:
        """Get QA metadata without creating JSONL files."""
        if not benchmark_path.exists() or not benchmark_path.is_dir():
            return None

        # Detect language
        language = self.detect_language(benchmark_path)
        if not language:
            return None

        # Generate language-specific metadata
        try:
            if language == "verus":
                return self.generate_verus_metadata(benchmark_path)
            elif language == "dafny":
                return self.generate_dafny_metadata(benchmark_path)
            elif language == "lean":
                return self.generate_lean_metadata(benchmark_path)
        except Exception as e:
            if not self.quiet:
                print(f"Error generating metadata for {benchmark_path}: {e}")
            return None

        return None


def get_qa_metadata(
    benchmark_path: str, config_path: Optional[str] = None, quiet: bool = True
) -> Optional[Dict]:
    """
    Convenience function to get QA metadata for a benchmark.

    Args:
        benchmark_path: Path to benchmark directory
        config_path: Optional path to custom configuration file
        quiet: Whether to suppress output

    Returns:
        Dictionary containing QA metadata or None if failed
    """
    generator = QAMetadataGenerator(
        quiet=quiet, config_path=Path(config_path) if config_path else None
    )
    return generator.get_metadata_only(Path(benchmark_path))


def get_all_qa_metadata(
    benchmarks_root: str, config_path: Optional[str] = None, quiet: bool = True
) -> Dict[str, Dict]:
    """
    Convenience function to get QA metadata for all benchmarks in a directory.

    Args:
        benchmarks_root: Path to benchmarks root directory
        config_path: Optional path to custom configuration file
        quiet: Whether to suppress output

    Returns:
        Dictionary mapping benchmark paths to their QA metadata
    """
    generator = QAMetadataGenerator(
        quiet=quiet, config_path=Path(config_path) if config_path else None
    )
    success, all_metadata = generator.process_benchmarks_directory(
        Path(benchmarks_root)
    )
    return all_metadata if success else {}


def load_benchmark_with_metadata(
    benchmark_jsonl_path: str,
) -> Tuple[List[Dict], Optional[Dict]]:
    """
    Load a benchmark JSONL file along with its metadata.

    Args:
        benchmark_jsonl_path: Path to the benchmark JSONL file

    Returns:
        Tuple of (entries_list, metadata_dict) or (entries_list, None) if no metadata
    """
    jsonl_path = Path(benchmark_jsonl_path)
    metadata_path = jsonl_path.parent / f"{jsonl_path.stem}.metadata.json"

    # Load entries
    entries = []
    try:
        with open(jsonl_path, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line:
                    entries.append(json.loads(line))
    except Exception as e:
        print(f"Error loading JSONL file {jsonl_path}: {e}")
        return [], None

    # Load metadata if exists
    metadata = None
    if metadata_path.exists():
        try:
            with open(metadata_path, "r", encoding="utf-8") as f:
                metadata = json.load(f)
        except Exception as e:
            print(f"Warning: Could not load metadata from {metadata_path}: {e}")

    return entries, metadata


def get_benchmark_quality_score(benchmark_jsonl_path: str) -> Optional[float]:
    """
    Get the quality score for a benchmark.

    Args:
        benchmark_jsonl_path: Path to the benchmark JSONL file

    Returns:
        Quality score or None if not available
    """
    _, metadata = load_benchmark_with_metadata(benchmark_jsonl_path)
    if metadata and "qa_metadata" in metadata:
        return metadata["qa_metadata"].get("score")
    return None


def list_benchmarks_with_metadata(benchmarks_root: str) -> List[Dict[str, str]]:
    """
    List all benchmarks that have metadata files.

    Args:
        benchmarks_root: Path to benchmarks root directory

    Returns:
        List of dictionaries with benchmark info
    """
    benchmarks_path = Path(benchmarks_root)
    benchmark_info = []

    for metadata_file in benchmarks_path.rglob("*.metadata.json"):
        # Extract base name by removing .metadata.json suffix
        base_name = metadata_file.name.replace(".metadata.json", "")
        jsonl_file = metadata_file.parent / f"{base_name}.jsonl"
        if jsonl_file.exists():
            try:
                with open(metadata_file, "r", encoding="utf-8") as f:
                    metadata = json.load(f)

                benchmark_info.append(
                    {
                        "jsonl_path": str(jsonl_file),
                        "metadata_path": str(metadata_file),
                        "language": metadata.get("benchmark_info", {}).get(
                            "language", "unknown"
                        ),
                        "name": metadata.get("benchmark_info", {}).get(
                            "name", "unknown"
                        ),
                        "score": metadata.get("qa_metadata", {}).get("score", 0),
                        "entry_count": metadata.get("benchmark_info", {}).get(
                            "entry_count", 0
                        ),
                    }
                )
            except Exception as e:
                print(f"Warning: Could not read metadata from {metadata_file}: {e}")

    return sorted(benchmark_info, key=lambda x: (x["language"], x["name"]))


def main():
    parser = argparse.ArgumentParser(
        description="Generate quality analysis metadata and per-entry scoring for benchmark JSONL files",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 add_qa_metadata.py benchmarks                    # Generate metadata for all benchmarks
  python3 add_qa_metadata.py benchmarks/verus/apps        # Generate metadata for specific benchmark
  python3 add_qa_metadata.py benchmarks/dafny/humaneval   # Generate metadata for Dafny benchmark
  python3 add_qa_metadata.py --quiet benchmarks           # Minimal output
  python3 add_qa_metadata.py --config custom.yaml benchmarks  # Use custom config
  
  # Output metadata in different formats
  python3 add_qa_metadata.py --output-metadata summary benchmarks    # Brief summary
  python3 add_qa_metadata.py --output-metadata json benchmarks       # Full JSON output
  
  # Metadata-only mode (skip enhanced JSONL generation)
  python3 add_qa_metadata.py --metadata-only benchmarks              # Only regenerate *.metadata.json

  # Output files generated/overwritten:
  #   Original:     benchmarks/verus/humaneval/verus_humaneval.jsonl (unchanged)
  #   Benchmark:    benchmarks/verus/humaneval/verus_humaneval.metadata.json  
  #   Per-entry:    benchmarks/verus/humaneval/verus_humaneval_with_entry_qa.jsonl
        """,
    )

    parser.add_argument(
        "benchmark_path", help="Path to benchmarks directory or specific benchmark"
    )
    parser.add_argument(
        "--quiet", action="store_true", help="Quiet mode: minimal output"
    )
    parser.add_argument(
        "--config",
        type=Path,
        help="Path to custom configuration file (default: qa_config.yaml)",
    )
    parser.add_argument(
        "--output-metadata",
        choices=["none", "json", "summary"],
        default="none",
        help="Output format for metadata (none: no output, json: full JSON, summary: brief summary)",
    )
    parser.add_argument(
        "--metadata-only",
        action="store_true",
        help="Generate only *.metadata.json files, skip *_with_entry_qa.jsonl generation",
    )

    args = parser.parse_args()

    # Create generator and process benchmarks
    generator = QAMetadataGenerator(
        quiet=args.quiet, config_path=args.config, metadata_only=args.metadata_only
    )
    benchmark_path = Path(args.benchmark_path)

    success, all_metadata = generator.process_benchmarks_directory(benchmark_path)

    # Output metadata if requested
    if args.output_metadata != "none" and all_metadata:
        if args.output_metadata == "json":
            print("\n" + "=" * 50)
            print("QA METADATA (JSON)")
            print("=" * 50)
            print(json.dumps(all_metadata, indent=2))
        elif args.output_metadata == "summary":
            print("\n" + "=" * 50)
            print("QA METADATA SUMMARY")
            print("=" * 50)
            for benchmark_path, metadata in all_metadata.items():
                print(f"\n📁 {benchmark_path}")
                print(f"   Base Score: {metadata.get('base_score', 'N/A')}")
                print(f"   Final Score: {metadata.get('score', 'N/A')}")

                # Language-specific summary
                if "specs_with_default_values" in metadata:  # Verus
                    print(
                        f"   Specs with defaults: {len(metadata.get('specs_with_default_values', []))}"
                    )
                    print(
                        f"   Execs with bodies: {len(metadata.get('execs_with_bodies', []))}"
                    )
                    print(
                        f"   Execs with ghost types: {len(metadata.get('execs_with_ghost_types', []))}"
                    )
                elif "functions_with_default_values" in metadata:  # Dafny
                    print(
                        f"   Functions with defaults: {len(metadata.get('functions_with_default_values', []))}"
                    )
                    print(
                        f"   Methods with bodies: {len(metadata.get('methods_with_bodies', []))}"
                    )
                elif "definitions_with_sorry" in metadata:  # Lean
                    print(
                        f"   Definitions with sorry: {len(metadata.get('definitions_with_sorry', []))}"
                    )

                # Near duplicates (all languages)
                near_dups = metadata.get("near_duplicates", {})
                print(f"   Near duplicates: {near_dups.get('total_count', 0)}")

    if success:
        if not args.quiet:
            print("\n✅ QA metadata generation completed successfully!")
        sys.exit(0)
    else:
        if not args.quiet:
            print("\n❌ QA metadata generation failed!")
        sys.exit(1)


if __name__ == "__main__":
    main()
