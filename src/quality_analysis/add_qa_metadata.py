#!/usr/bin/env python3
"""
Add quality analysis metadata to benchmark JSONL files.

This script analyzes benchmark directories and adds QA metadata to each entry
in the corresponding JSONL file. The metadata includes quality metrics specific
to each language (Verus, Dafny, Lean) based on specification quality and similarity analysis.
It can also return the metadata directly for programmatic use.

For specifications, we expect:
- Verus: assume(false); unreached() in executable functions, meaningful spec functions
- Dafny: assume {:axiom} false in methods, meaningful function/predicate specifications
- Lean: proper implementations without sorry
- All languages: minimal near-duplicate content for diversity

Usage:
    # Command line usage
    python3 add_qa_metadata.py benchmarks                    # Process all benchmarks
    python3 add_qa_metadata.py benchmarks/verus/apps        # Process specific benchmark
    python3 add_qa_metadata.py --config custom_config.yaml  # Use custom configuration
    python3 add_qa_metadata.py --output-metadata summary benchmarks  # Show metadata summary
    python3 add_qa_metadata.py --output-metadata json benchmarks     # Output full JSON

    # Programmatic usage
    from add_qa_metadata import get_qa_metadata, get_all_qa_metadata

    # Get metadata for single benchmark
    metadata = get_qa_metadata("benchmarks/verus/numpy_triple")

    # Get metadata for all benchmarks
    all_metadata = get_all_qa_metadata("benchmarks")
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
import yaml

# Import similarity analysis
try:
    from optimized_vector_similarity import get_near_duplicates_for_benchmark

    SIMILARITY_AVAILABLE = True
except ImportError:
    SIMILARITY_AVAILABLE = False


class QAMetadataGenerator:
    def __init__(self, quiet: bool = False, config_path: Optional[Path] = None):
        self.quiet = quiet
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
        """Find JSONL files in benchmark directory."""
        jsonl_files = list(benchmark_path.glob("*.jsonl"))

        # Filter out files that already have QA metadata
        original_files = [
            f for f in jsonl_files if not f.name.endswith("_with_qa_metadata.jsonl")
        ]

        if not original_files:
            self.log(f"No JSONL files found in {benchmark_path}")

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
                except json.JSONDecodeError:
                    self.log(f"Warning: Could not parse JSON output from {script_name}")
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
        if not SIMILARITY_AVAILABLE:
            self.log(
                "Warning: Similarity analysis not available (missing dependencies)"
            )
            return {"examples": [], "total_count": 0}

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

            # Calculate score using config values and dynamic base score
            scoring_config = self.config["scoring"]
            verus_config = scoring_config["verus"]

            specs_penalty = (
                len(metadata["specs_with_default_values"])
                * verus_config["specs_with_default_values_penalty"]
            )
            bodies_penalty = (
                len(metadata["execs_with_bodies"])
                * verus_config["execs_with_bodies_penalty"]
            )
            types_penalty = (
                len(metadata["execs_with_ghost_types"])
                * verus_config["execs_with_ghost_types_penalty"]
            )
            similarity_penalty = (
                similarity_data["total_count"] * verus_config["near_duplicates_penalty"]
            )

            base_score = self.get_base_score_for_benchmark(benchmark_path)
            metadata["base_score"] = base_score
            metadata["score"] = max(
                0,
                base_score
                - specs_penalty
                - bodies_penalty
                - types_penalty
                - similarity_penalty,
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

            # Calculate score using config values and dynamic base score
            scoring_config = self.config["scoring"]
            dafny_config = scoring_config["dafny"]

            func_penalty = (
                len(metadata["functions_with_default_values"])
                * dafny_config["functions_with_default_values_penalty"]
            )
            method_penalty = (
                len(metadata["methods_with_bodies"])
                * dafny_config["methods_with_bodies_penalty"]
            )
            similarity_penalty = (
                similarity_data["total_count"] * dafny_config["near_duplicates_penalty"]
            )

            base_score = self.get_base_score_for_benchmark(benchmark_path)
            metadata["base_score"] = base_score
            metadata["score"] = max(
                0, base_score - func_penalty - method_penalty - similarity_penalty
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

            # Calculate score using config values and dynamic base score
            scoring_config = self.config["scoring"]
            lean_config = scoring_config["lean"]

            sorry_penalty = (
                len(metadata["definitions_with_sorry"])
                * lean_config["definitions_with_sorry_penalty"]
            )
            similarity_penalty = (
                similarity_data["total_count"] * lean_config["near_duplicates_penalty"]
            )

            base_score = self.get_base_score_for_benchmark(benchmark_path)
            metadata["base_score"] = base_score
            metadata["score"] = max(0, base_score - sorry_penalty - similarity_penalty)

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

    def process_jsonl_file(
        self, jsonl_path: Path, benchmark_path: Path, language: str
    ) -> Tuple[bool, Optional[Dict]]:
        """Process a single JSONL file and add QA metadata."""
        output_path = jsonl_path.parent / f"{jsonl_path.stem}_with_qa_metadata.jsonl"

        self.log(f"Processing {jsonl_path.name} -> {output_path.name}")

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

            # Process JSONL file
            with (
                open(jsonl_path, "r", encoding="utf-8") as infile,
                open(output_path, "w", encoding="utf-8") as outfile,
            ):
                for line_num, line in enumerate(infile, 1):
                    line = line.strip()
                    if not line:
                        continue

                    try:
                        entry = json.loads(line)
                        entry["qa_metadata"] = qa_metadata
                        outfile.write(json.dumps(entry) + "\n")

                    except json.JSONDecodeError as e:
                        self.log(
                            f"Warning: Could not parse line {line_num} in {jsonl_path}: {e}"
                        )
                        continue

            self.log(f"✅ Created {output_path}")
            return True, qa_metadata

        except Exception as e:
            self.log(f"❌ Error processing {jsonl_path}: {e}")
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

        # Process each JSONL file
        success_count = 0
        qa_metadata = None
        for jsonl_file in jsonl_files:
            success, metadata = self.process_jsonl_file(
                jsonl_file, benchmark_path, language
            )
            if success:
                success_count += 1
                qa_metadata = (
                    metadata  # Store the metadata (same for all files in benchmark)
                )

        self.log(
            f"Processed {success_count}/{len(jsonl_files)} JSONL files in {benchmark_path}"
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
        jsonl_files = self.find_jsonl_files(benchmarks_root)
        if jsonl_files:
            # This directory contains JSONL files, treat as single benchmark
            success, metadata = self.process_benchmark(benchmarks_root)
            if success and metadata:
                all_metadata[str(benchmarks_root)] = metadata
            return success, all_metadata

        # This is a benchmarks root, find all benchmark subdirectories
        benchmark_dirs = []
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


def main():
    parser = argparse.ArgumentParser(
        description="Add quality analysis metadata to benchmark JSONL files",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 add_qa_metadata.py benchmarks                    # Process all benchmarks
  python3 add_qa_metadata.py benchmarks/verus/apps        # Process specific benchmark
  python3 add_qa_metadata.py benchmarks/dafny/humaneval   # Process Dafny benchmark
  python3 add_qa_metadata.py --quiet benchmarks           # Minimal output
  python3 add_qa_metadata.py --config custom.yaml benchmarks  # Use custom config
  
  # Output metadata in different formats
  python3 add_qa_metadata.py --output-metadata summary benchmarks    # Brief summary
  python3 add_qa_metadata.py --output-metadata json benchmarks       # Full JSON output
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

    args = parser.parse_args()

    # Create generator and process benchmarks
    generator = QAMetadataGenerator(quiet=args.quiet, config_path=args.config)
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
