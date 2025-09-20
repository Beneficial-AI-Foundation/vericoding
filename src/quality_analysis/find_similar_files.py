#!/usr/bin/env python3
"""
Script to identify duplicate and very similar files across verification benchmarks.

This script uses multiple strategies to detect file similarity:
1. Exact duplicates (same content hash)
2. Structural similarity (same YAML structure, similar code)
3. Content similarity (similar text with fuzzy matching)

The goal is to identify candidate files for removal to deduplicate datasets
while preserving meaningful variations.

Usage:
    python3 find_similar_files.py                        # Analyze default directories
    python3 find_similar_files.py --dir /path/to/files   # Custom directory
    python3 find_similar_files.py --similarity-threshold 0.9  # Adjust similarity threshold
    python3 find_similar_files.py --help                 # Show all options

Output:
- exact_duplicates.txt: Files with identical content
- similar_files_candidates.txt: Files that are very similar (candidates for removal)
- similarity_analysis_report.txt: Detailed analysis report
- Console summary with statistics

Similarity Detection Methods:
1. **Exact duplicates**: MD5 hash comparison
2. **YAML structure**: Compare vc-description, vc-spec, vc-code sections
3. **Code similarity**: Fuzzy string matching on code content
4. **Filename patterns**: Detect systematically generated duplicates
"""

import os
import hashlib
import re
import argparse
import yaml
from pathlib import Path
from typing import List, Dict
from difflib import SequenceMatcher
from collections import defaultdict


def calculate_file_hash(file_path: Path) -> str:
    """Calculate MD5 hash of file content."""
    try:
        with open(file_path, "rb") as f:
            return hashlib.md5(f.read()).hexdigest()
    except Exception:
        return ""


def normalize_code_content(content: str) -> str:
    """Normalize code content for comparison by removing comments and extra whitespace."""
    # Remove single-line comments
    content = re.sub(r"//.*$", "", content, flags=re.MULTILINE)
    # Remove block comments
    content = re.sub(r"/\*.*?\*/", "", content, flags=re.DOTALL)
    # Remove extra whitespace
    content = re.sub(r"\s+", " ", content)
    # Remove empty lines
    content = re.sub(r"\n\s*\n", "\n", content)
    return content.strip()


def extract_yaml_sections(file_path: Path) -> Dict[str, str]:
    """Extract key sections from YAML files for comparison.

    Note: Excludes vc-code and vc-postamble sections since they're typically
    the same across files (vc-code is usually 'assume {:axiom} false;' and
    vc-postamble is usually empty).
    """
    try:
        with open(file_path, "r", encoding="utf-8") as f:
            data = yaml.safe_load(f)

        if not data:
            return {}

        sections = {}
        # Focus on the sections that actually vary between files
        for key in ["vc-description", "vc-preamble", "vc-spec"]:
            if key in data:
                content = data[key]
                if content:
                    sections[key] = normalize_code_content(str(content))

        return sections
    except Exception:
        return {}


def calculate_text_similarity(
    text1: str, text2: str, method: str = "character"
) -> float:
    """Calculate similarity ratio between two text strings."""
    if not text1 and not text2:
        return 1.0
    if not text1 or not text2:
        return 0.0

    if method == "character":
        return SequenceMatcher(None, text1, text2).ratio()
    elif method == "semantic_hash":
        return calculate_semantic_hash_similarity(text1, text2)
    elif method == "jaccard":
        return calculate_jaccard_similarity(text1, text2)
    elif method == "cosine":
        return calculate_cosine_similarity(text1, text2)
    else:
        return SequenceMatcher(None, text1, text2).ratio()


def calculate_semantic_hash_similarity(
    text1: str, text2: str, fallback_threshold: float = 0.95
) -> float:
    """
    Hybrid similarity: structural hash + high-threshold character similarity.

    This approach:
    1. Normalizes text to focus on problem structure, not specific implementations
    2. Checks if normalized versions are identical (hash match = 1.0)
    3. Falls back to character similarity with high threshold if not identical

    This distinguishes "implement quicksort" from "implement radix sort" while
    still catching true duplicates and very similar descriptions.
    """
    import re

    def normalize_structure(text: str) -> str:
        """Normalize text to focus on problem structure."""
        text = text.strip().lower()

        # Replace specific algorithm names with generic placeholder
        # But be more precise about it
        sort_algorithms = (
            r"\b(radix|quick|merge|heap|bubble|insertion|selection|tim)(sort|_sort)?\b"
        )
        text = re.sub(sort_algorithms, "SORT_ALGORITHM", text)

        # Replace specific search algorithms
        search_algorithms = r"\b(binary|linear|depth|breadth)(search|_search)?\b"
        text = re.sub(search_algorithms, "SEARCH_ALGORITHM", text)

        # Don't normalize method names too aggressively - only if they're clearly algorithmic

        # Normalize common sorting/ordering terms
        text = re.sub(r"\bsort(ing|ed)?\b", "sort", text)
        text = re.sub(r"\border(ing|ed)?\b", "order", text)

        return text.strip()

    # First: Check structural similarity via hash
    struct1 = normalize_structure(text1)
    struct2 = normalize_structure(text2)

    if struct1 == struct2:
        return 1.0  # Structurally identical

    # Second: Fall back to character similarity with high threshold
    char_sim = SequenceMatcher(None, text1.lower(), text2.lower()).ratio()
    return char_sim if char_sim >= fallback_threshold else 0.0


def tokenize_text(text: str) -> List[str]:
    """Tokenize text into words for similarity calculations."""
    import re

    text = text.lower()
    # Split on spaces and punctuation, keep alphanumeric
    tokens = re.findall(r"\b\w+\b", text)
    return tokens


def calculate_jaccard_similarity(text1: str, text2: str) -> float:
    """
    Calculate Jaccard similarity: intersection over union of word sets.

    Perfect for detecting rephrasings with different word orders.
    Example: "sort elements" vs "elements to sort" = high similarity
    """
    tokens1 = set(tokenize_text(text1))
    tokens2 = set(tokenize_text(text2))

    intersection = len(tokens1 & tokens2)
    union = len(tokens1 | tokens2)

    return intersection / union if union > 0 else 0.0


def calculate_cosine_similarity(text1: str, text2: str) -> float:
    """
    Calculate cosine similarity: dot product of normalized word frequency vectors.

    Excellent for detecting rephrasings that preserve semantic content.
    Handles repeated words and slight variations gracefully.
    """
    import math
    from collections import Counter

    tokens1 = tokenize_text(text1)
    tokens2 = tokenize_text(text2)

    # Get word frequencies
    freq1 = Counter(tokens1)
    freq2 = Counter(tokens2)

    # Get all unique words
    all_words = set(freq1.keys()) | set(freq2.keys())

    # Create vectors
    vec1 = [freq1.get(word, 0) for word in all_words]
    vec2 = [freq2.get(word, 0) for word in all_words]

    # Calculate cosine similarity
    dot_product = sum(a * b for a, b in zip(vec1, vec2))
    magnitude1 = math.sqrt(sum(a * a for a in vec1))
    magnitude2 = math.sqrt(sum(b * b for b in vec2))

    if magnitude1 == 0 or magnitude2 == 0:
        return 0.0

    return dot_product / (magnitude1 * magnitude2)


def calculate_yaml_similarity(
    sections1: Dict[str, str],
    sections2: Dict[str, str],
    weight_focus: str = "description",
    similarity_method: str = "auto",
) -> float:
    """Calculate similarity between YAML sections."""
    if not sections1 and not sections2:
        return 1.0
    if not sections1 or not sections2:
        return 0.0

    # Define weight configurations based on focus area
    weight_configs = {
        "balanced": {"vc-description": 0.3, "vc-preamble": 0.4, "vc-spec": 0.3},
        "description": {
            "vc-description": 0.4,  # Focus on problem descriptions
            "vc-preamble": 0.4,
            "vc-spec": 0.2,
        },
        "preamble": {
            "vc-description": 0.1,
            "vc-preamble": 0.8,  # Focus on helper functions
            "vc-spec": 0.1,
        },
        "spec": {
            "vc-description": 0.1,
            "vc-preamble": 0.1,
            "vc-spec": 0.8,  # Focus on method specifications
        },
        "description-only": {
            "vc-description": 1.0,  # Only consider problem descriptions
            "vc-preamble": 0.0,
            "vc-spec": 0.0,
        },
    }

    weights = weight_configs.get(weight_focus, weight_configs["description"])

    total_similarity = 0.0
    total_weight = 0.0

    for section in set(sections1.keys()) | set(sections2.keys()):
        weight = weights.get(section, 0.1)
        total_weight += weight

        content1 = sections1.get(section, "")
        content2 = sections2.get(section, "")

        # Determine similarity method
        if similarity_method == "auto":
            sim_method = (
                "semantic_hash" if weight_focus == "description-only" else "character"
            )
        else:
            sim_method = similarity_method

        similarity = calculate_text_similarity(content1, content2, sim_method)
        total_similarity += similarity * weight

    return total_similarity / total_weight if total_weight > 0 else 0.0


def detect_filename_patterns(files: List[Path]) -> Dict[str, List[Path]]:
    """Detect files that follow similar naming patterns (likely auto-generated)."""
    pattern_groups = defaultdict(list)

    for file_path in files:
        filename = file_path.name

        # Only look for very specific duplicate patterns that suggest auto-generation
        base_patterns = []

        # Look for explicit version/copy patterns
        if re.search(r"_v\d+\.", filename):  # _v1, _v2, etc.
            base_patterns.append(re.sub(r"_v\d+\.", "_vXXX.", filename))

        if re.search(r"_copy\d*\.", filename):  # _copy, _copy1, _copy2, etc.
            base_patterns.append(re.sub(r"_copy\d*\.", "_copyXXX.", filename))

        if re.search(r"_backup\d*\.", filename):  # _backup, _backup1, etc.
            base_patterns.append(re.sub(r"_backup\d*\.", "_backupXXX.", filename))

        if re.search(r"_old\d*\.", filename):  # _old, _old1, etc.
            base_patterns.append(re.sub(r"_old\d*\.", "_oldXXX.", filename))

        if re.search(r"_new\d*\.", filename):  # _new, _new1, etc.
            base_patterns.append(re.sub(r"_new\d*\.", "_newXXX.", filename))

        # Look for files with same name but different extensions (less common but possible)
        if filename.count(".") > 1:  # file.ext1.ext2
            base_pattern = ".".join(filename.split(".")[:-1]) + ".XXX"
            base_patterns.append(base_pattern)

        for pattern in base_patterns:
            if pattern != filename:  # Only if we actually found a pattern
                pattern_groups[pattern].append(file_path)

    # Only return groups with multiple files (at least 3 to be conservative)
    return {
        pattern: files for pattern, files in pattern_groups.items() if len(files) >= 3
    }


def find_similar_files(
    directory: str,
    similarity_threshold: float = 0.85,
    include_exact_duplicates: bool = True,
    file_type: str = "yaml",
    weight_focus: str = "description",
    similarity_method: str = "auto",
) -> Dict[str, List]:
    """
    Find similar files in the directory.

    Returns:
        dict with keys: 'exact_duplicates', 'similar_files', 'pattern_groups'
    """
    print(f"Scanning directory: {directory}")
    print(f"File type filter: {file_type}")

    # Define file extensions based on type
    if file_type == "yaml":
        file_extensions = {".yaml", ".yml"}
    elif file_type == "dfy":
        file_extensions = {".dfy"}
    elif file_type == "rs":
        file_extensions = {".rs"}
    elif file_type == "lean":
        file_extensions = {".lean"}
    else:  # "all"
        file_extensions = {".yaml", ".yml", ".dfy", ".rs", ".lean"}

    all_files = []

    for root, _, files in os.walk(directory):
        for file in files:
            file_path = Path(root) / file
            if file_path.suffix.lower() in file_extensions:
                all_files.append(file_path)

    print(f"Found {len(all_files)} files to analyze")

    # Group files by hash for exact duplicates
    hash_groups = defaultdict(list)
    yaml_sections = {}

    for file_path in all_files:
        file_hash = calculate_file_hash(file_path)
        if file_hash:
            hash_groups[file_hash].append(file_path)

        # Extract YAML sections for similarity comparison
        if file_path.suffix.lower() in {".yaml", ".yml"}:
            sections = extract_yaml_sections(file_path)
            if sections:
                yaml_sections[file_path] = sections

    # Find exact duplicates
    exact_duplicates = {
        hash_val: files for hash_val, files in hash_groups.items() if len(files) > 1
    }

    # Find similar files (non-exact)
    similar_groups = []
    processed_files = set()

    # First, mark exact duplicates as processed
    for files in exact_duplicates.values():
        processed_files.update(files)

    # Compare YAML files for similarity
    yaml_files = list(yaml_sections.keys())
    for i, file1 in enumerate(yaml_files):
        if file1 in processed_files:
            continue

        similar_to_file1 = [file1]

        for j, file2 in enumerate(yaml_files[i + 1 :], i + 1):
            if file2 in processed_files:
                continue

            similarity = calculate_yaml_similarity(
                yaml_sections[file1],
                yaml_sections[file2],
                weight_focus,
                similarity_method,
            )

            if similarity >= similarity_threshold:
                similar_to_file1.append(file2)
                processed_files.add(file2)

        if len(similar_to_file1) > 1:
            similar_groups.append(similar_to_file1)
            processed_files.update(similar_to_file1)

    # Detect filename patterns
    pattern_groups = detect_filename_patterns(all_files)

    return {
        "exact_duplicates": exact_duplicates,
        "similar_files": similar_groups,
        "pattern_groups": pattern_groups,
        "total_files": len(all_files),
    }


def select_removal_candidates(results: Dict) -> List[Path]:
    """
    Select which files should be candidates for removal.

    Strategy:
    1. For exact duplicates: keep the first one (alphabetically), remove others
    2. For similar files: keep the shortest filename, remove others
    3. For pattern groups: keep one representative, remove others
    """
    removal_candidates = []

    # Exact duplicates: keep first alphabetically
    for hash_val, files in results["exact_duplicates"].items():
        sorted_files = sorted(files, key=lambda x: str(x))
        removal_candidates.extend(sorted_files[1:])  # Remove all but first

    # Similar files: keep file with shortest name (likely most canonical)
    for group in results["similar_files"]:
        if len(group) > 1:
            sorted_by_length = sorted(group, key=lambda x: (len(x.name), str(x)))
            removal_candidates.extend(sorted_by_length[1:])  # Remove all but first

    # Pattern groups: keep one per pattern
    for pattern, files in results["pattern_groups"].items():
        if len(files) > 1:
            sorted_files = sorted(files, key=lambda x: str(x))
            removal_candidates.extend(sorted_files[1:])  # Remove all but first

    # Remove duplicates from candidates list
    return list(set(removal_candidates))


def generate_report(results: Dict, removal_candidates: List[Path], output_dir: str):
    """Generate detailed analysis report."""
    report_path = Path(output_dir) / "similarity_analysis_report.txt"

    with open(report_path, "w") as f:
        f.write("# File Similarity Analysis Report\n")
        f.write("=" * 50 + "\n\n")

        f.write(f"Total files analyzed: {results['total_files']}\n")
        f.write(f"Exact duplicate groups: {len(results['exact_duplicates'])}\n")
        f.write(f"Similar file groups: {len(results['similar_files'])}\n")
        f.write(f"Pattern groups: {len(results['pattern_groups'])}\n")
        f.write(f"Total removal candidates: {len(removal_candidates)}\n\n")

        # Exact duplicates
        if results["exact_duplicates"]:
            f.write("## Exact Duplicates\n")
            for i, (hash_val, files) in enumerate(
                results["exact_duplicates"].items(), 1
            ):
                f.write(f"\nGroup {i} (hash: {hash_val[:8]}...):\n")
                for file_path in files:
                    status = "KEEP" if file_path not in removal_candidates else "REMOVE"
                    f.write(f"  [{status}] {file_path}\n")

        # Similar files
        if results["similar_files"]:
            f.write("\n## Similar Files\n")
            for i, group in enumerate(results["similar_files"], 1):
                f.write(f"\nGroup {i}:\n")
                for file_path in group:
                    status = "KEEP" if file_path not in removal_candidates else "REMOVE"
                    f.write(f"  [{status}] {file_path}\n")

        # Pattern groups
        if results["pattern_groups"]:
            f.write("\n## Pattern Groups\n")
            for pattern, files in results["pattern_groups"].items():
                f.write(f"\nPattern '{pattern}':\n")
                for file_path in files:
                    status = "KEEP" if file_path not in removal_candidates else "REMOVE"
                    f.write(f"  [{status}] {file_path}\n")

    print(f"📄 Detailed report written to: {report_path}")


def main():
    """Main function to find similar files."""
    parser = argparse.ArgumentParser(
        description="Find duplicate and similar files in verification benchmarks",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python3 find_similar_files.py                           # Analyze YAML files, focus on descriptions
  python3 find_similar_files.py --weight-focus description-only # ONLY consider problem descriptions
  python3 find_similar_files.py --similarity-method jaccard      # Use Jaccard similarity for rephrasings
  python3 find_similar_files.py --similarity-method cosine       # Use cosine similarity for semantic matching
  python3 find_similar_files.py --similarity-method semantic_hash # Use structural hashing (precise)
  python3 find_similar_files.py --similarity-threshold 0.9        # Higher similarity threshold
        """,
    )

    parser.add_argument(
        "--dir",
        default="/home/lacra/git_repos/baif/vericoding/benchmarks",
        help="Directory to analyze (default: %(default)s)",
    )
    parser.add_argument(
        "--similarity-threshold",
        type=float,
        default=0.85,
        help="Similarity threshold for detecting similar files (0.0-1.0, default: %(default)s)",
    )
    parser.add_argument(
        "--output-dir",
        default=".",
        help="Directory for output files (default: current directory)",
    )
    parser.add_argument(
        "--exclude-dirs",
        nargs="*",
        default=["poor", "non_compiling", "problematic", "temp", "temporary"],
        help="Directory names to exclude from analysis",
    )
    parser.add_argument(
        "--file-type",
        choices=["yaml", "dfy", "rs", "lean", "all"],
        default="yaml",
        help="File type to analyze (default: %(default)s)",
    )
    parser.add_argument(
        "--weight-focus",
        choices=["balanced", "description", "description-only", "preamble", "spec"],
        default="description",
        help="Focus area for similarity weighting (default: %(default)s)",
    )
    parser.add_argument(
        "--similarity-method",
        choices=[
            "auto",
            "character",
            "semantic_hash",
            "jaccard",
            "cosine",
            "vector_embedding",
            "hybrid_vector",
        ],
        default="auto",
        help="Similarity calculation method (auto=semantic_hash for description-only, character otherwise)",
    )
    parser.add_argument(
        "--embedding-focus",
        choices=["semantic", "structural", "balanced"],
        default="semantic",
        help="Focus area for vector embeddings (semantic=problem understanding, structural=code patterns)",
    )
    parser.add_argument(
        "--use-vector-index",
        action="store_true",
        help="Use FAISS indexing for efficient vector similarity search (recommended for >100 files)",
    )

    args = parser.parse_args()

    if not os.path.exists(args.dir):
        print(f"Error: Directory {args.dir} does not exist")
        return

    print("🔍 Finding duplicate and similar files...")
    print("=" * 60)

    # Check if vector methods are requested
    if args.similarity_method in ["vector_embedding", "hybrid_vector"]:
        try:
            from vector_enhanced_similarity import enhanced_find_similar_files

            print("🚀 Using vector-enhanced similarity detection...")
            results = enhanced_find_similar_files(
                args.dir,
                similarity_threshold=args.similarity_threshold,
                similarity_method=args.similarity_method,
                embedding_focus=args.embedding_focus,
                use_vector_index=args.use_vector_index,
            )
            # Convert to expected format
            results["exact_duplicates"] = {}
            results["pattern_groups"] = {}
        except ImportError as e:
            print(f"❌ Vector similarity not available: {e}")
            print(
                "Install with: pip install sentence-transformers scikit-learn faiss-cpu"
            )
            print("Falling back to traditional similarity detection...")
            results = find_similar_files(
                args.dir,
                similarity_threshold=args.similarity_threshold,
                file_type=args.file_type,
                weight_focus=args.weight_focus,
                similarity_method="semantic_hash",  # Safe fallback
            )
    else:
        # Use traditional similarity detection
        results = find_similar_files(
            args.dir,
            similarity_threshold=args.similarity_threshold,
            file_type=args.file_type,
            weight_focus=args.weight_focus,
            similarity_method=args.similarity_method,
        )

    # Select removal candidates
    removal_candidates = select_removal_candidates(results)

    # Print summary
    print("\n" + "=" * 60)
    print("SUMMARY:")
    print(f"Total files analyzed: {results['total_files']}")
    print(f"Exact duplicate groups: {len(results['exact_duplicates'])}")
    print(f"Similar file groups: {len(results['similar_files'])}")
    print(f"Pattern groups: {len(results['pattern_groups'])}")
    print(f"Total removal candidates: {len(removal_candidates)}")

    if removal_candidates:
        # Calculate space that could be saved
        total_duplicate_files = sum(
            len(files) - 1 for files in results["exact_duplicates"].values()
        )
        print(f"Exact duplicate files to remove: {total_duplicate_files}")
        print(
            f"Similar/pattern files to remove: {len(removal_candidates) - total_duplicate_files}"
        )

    # Write output files
    output_dir = Path(args.output_dir)

    # Exact duplicates list
    if results["exact_duplicates"]:
        exact_dups_file = output_dir / "exact_duplicates.txt"
        with open(exact_dups_file, "w") as f:
            f.write("# Exact duplicate files (candidates for removal)\n")
            f.write("# Format: one file per line\n\n")
            for files in results["exact_duplicates"].values():
                for file_path in sorted(files)[1:]:  # Skip first (keep it)
                    f.write(f"{file_path}\n")
        print(f"📄 Exact duplicates written to: {exact_dups_file}")

    # Similar files candidates
    if removal_candidates:
        candidates_file = output_dir / "similar_files_candidates.txt"
        with open(candidates_file, "w") as f:
            f.write("# Similar files candidates for removal\n")
            f.write(
                "# These files are very similar to other files and can likely be removed\n"
            )
            f.write("# Format: one file per line\n\n")
            for file_path in sorted(removal_candidates):
                f.write(f"{file_path}\n")
        print(f"📄 Removal candidates written to: {candidates_file}")

    # Generate detailed report
    generate_report(results, removal_candidates, args.output_dir)

    # Show examples
    if results["exact_duplicates"]:
        print("\nFirst 5 exact duplicate groups:")
        for i, (hash_val, files) in enumerate(
            list(results["exact_duplicates"].items())[:5], 1
        ):
            print(f"  Group {i}: {len(files)} files")
            for file_path in files[:2]:  # Show first 2
                print(f"    {file_path}")
            if len(files) > 2:
                print(f"    ... and {len(files) - 2} more")

    if results["similar_files"]:
        print("\nFirst 5 similar file groups:")
        for i, group in enumerate(results["similar_files"][:5], 1):
            print(f"  Group {i}: {len(group)} files")
            for file_path in group[:2]:  # Show first 2
                print(f"    {file_path}")
            if len(group) > 2:
                print(f"    ... and {len(group) - 2} more")

    if removal_candidates:
        print(
            "\n💡 Next step: Use move_similar_files.py to move candidates to a separate folder"
        )
        print(
            f"   python3 move_similar_files.py --candidate-file {output_dir / 'similar_files_candidates.txt'}"
        )
    else:
        print("\n✅ No similar files found - dataset appears to be clean!")


if __name__ == "__main__":
    main()
