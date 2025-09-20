#!/usr/bin/env python3
"""
YAML Similarity Scorer - Compare a single YAML file against a folder of YAML files.

This script takes a single YAML file and compares it against all YAML files in a specified
folder, returning similarity scores and identifying the most similar files.

Features:
- Semantic similarity using sentence transformers
- Batch processing for efficiency
- Caching for repeated comparisons
- Detailed similarity scores and rankings
- Support for different embedding focuses (semantic, structural, balanced)
"""

import os
import time
import pickle
import hashlib
import argparse
from pathlib import Path
from typing import List, Optional
from dataclasses import dataclass
import yaml

# Optional imports for optimization
try:
    from tqdm import tqdm

    HAS_TQDM = True
except ImportError:
    HAS_TQDM = False

    def tqdm(iterable, *args, **kwargs):
        return iterable


try:
    from sentence_transformers import SentenceTransformer
    from sklearn.metrics.pairwise import cosine_similarity
    import numpy as np
    import faiss

    VECTOR_AVAILABLE = True
except ImportError:
    VECTOR_AVAILABLE = False

    # Create a dummy numpy for type hints
    class _DummyNumpy:
        class ndarray:
            pass

    np = _DummyNumpy()


@dataclass
class SimilarityResult:
    """Result of similarity comparison between two YAML files."""

    file_path: Path
    similarity_score: float
    semantic_content: str


class YAMLSimilarityScorer:
    """
    Compare a single YAML file against a folder of YAML files using vector embeddings.

    This class provides efficient similarity scoring with caching and batch processing
    for comparing one YAML file against many others.
    """

    def __init__(
        self,
        embedding_model: str = "all-MiniLM-L6-v2",
        cache_dir: str = ".yaml_similarity_cache",
        use_gpu: bool = False,
    ):
        """
        Initialize the YAML similarity scorer.

        Args:
            embedding_model: SentenceTransformer model name
            cache_dir: Directory for caching embeddings
            use_gpu: Whether to use GPU acceleration
        """
        if not VECTOR_AVAILABLE:
            raise ImportError(
                "Vector libraries not available. Install with: "
                "uv add sentence-transformers scikit-learn numpy faiss-cpu"
            )

        self.cache_dir = Path(cache_dir)
        self.cache_dir.mkdir(exist_ok=True)

        # Initialize embedding model
        device = "cuda" if use_gpu else "cpu"
        self.embedding_model = SentenceTransformer(embedding_model, device=device)
        print(f"✅ Loaded {embedding_model} on {device}")

        # FAISS index for efficient similarity search
        self.faiss_index = None
        self.indexed_file_paths = []
        self.indexed_embeddings = {}

    def _get_cache_path(self, file_path: Path, focus: str) -> Path:
        """Get cache file path for a YAML file embedding."""
        cache_key = hashlib.md5(f"{file_path}_{focus}".encode()).hexdigest()
        return self.cache_dir / f"{cache_key}.pkl"

    def _is_cache_valid(self, file_path: Path, cache_path: Path) -> bool:
        """Check if cached embedding is still valid (file not modified)."""
        if not cache_path.exists():
            return False

        try:
            file_mtime = file_path.stat().st_mtime
            cache_mtime = cache_path.stat().st_mtime
            return cache_mtime > file_mtime
        except (OSError, IOError):
            return False

    def _extract_text_for_embedding(
        self, file_path: Path, focus: str = "semantic"
    ) -> str:
        """Extract and prepare text from YAML file for embedding."""
        try:
            with open(file_path, "r", encoding="utf-8") as f:
                data = yaml.safe_load(f)

            if not data:
                return ""

            # Extract relevant sections based on focus
            if focus == "semantic":
                parts = []
                if "vc-description" in data:
                    parts.append(f"Problem: {data['vc-description']}")
                if "vc-spec" in data:
                    # Normalize specification
                    spec = self._normalize_specification(str(data["vc-spec"]))
                    parts.append(f"Specification: {spec}")
                return " ".join(parts)
            elif focus == "structural":
                parts = []
                if "vc-preamble" in data:
                    parts.append(f"Helpers: {data['vc-preamble']}")
                if "vc-spec" in data:
                    parts.append(f"Spec: {data['vc-spec']}")
                if "vc-helpers" in data:
                    parts.append(f"Helpers: {data['vc-helpers']}")
                return " ".join(parts)
            else:  # balanced
                parts = []
                for key in ["vc-description", "vc-spec", "vc-preamble", "vc-helpers"]:
                    if key in data and data[key]:
                        parts.append(f"{key.replace('-', ' ').title()}: {data[key]}")
                return " ".join(parts)

        except Exception as e:
            print(f"Warning: Failed to extract from {file_path}: {e}")
            return ""

    def _normalize_specification(self, spec_text: str) -> str:
        """Normalize specification for better semantic understanding."""
        import re

        if not spec_text:
            return ""

        normalized = spec_text.lower()

        # Normalize verification patterns
        patterns = {
            r"\bensures?\b": "postcondition",
            r"\brequires?\b": "precondition",
            r"\bforall\b": "universal_quantifier",
            r"\bexists\b": "existential_quantifier",
            r"\bsorted\(\w*\)": "is_sorted",
            r"\.sorted\(\)": "is_sorted",
            r"\b\w*\.len\(\)": "length",
            r"\|\w*\|": "length",
        }

        for pattern, replacement in patterns.items():
            normalized = re.sub(pattern, replacement, normalized)

        return normalized

    def _get_or_create_embedding(
        self, file_path: Path, focus: str = "semantic"
    ) -> Optional[np.ndarray]:
        """Get embedding for a file, using cache if available."""
        cache_path = self._get_cache_path(file_path, focus)

        # Try to load from cache first
        if self._is_cache_valid(file_path, cache_path):
            try:
                with open(cache_path, "rb") as f:
                    return pickle.load(f)
            except (OSError, IOError, pickle.PickleError, EOFError):
                pass  # Cache corrupted, regenerate

        # Generate new embedding
        text = self._extract_text_for_embedding(file_path, focus)
        if not text.strip():
            return None

        try:
            embedding = self.embedding_model.encode([text], convert_to_numpy=True)[0]

            # Cache the embedding
            try:
                with open(cache_path, "wb") as f:
                    pickle.dump(embedding, f)
            except Exception as e:
                print(f"Warning: Failed to cache embedding for {file_path}: {e}")

            return embedding
        except Exception as e:
            print(f"Warning: Failed to generate embedding for {file_path}: {e}")
            return None

    def build_faiss_index(
        self, file_paths: List[Path], focus: str = "semantic"
    ) -> None:
        """
        Build FAISS index for efficient similarity search across multiple files.

        Args:
            file_paths: List of YAML file paths to index
            focus: Embedding focus type
        """
        print(f"🔧 Building FAISS index for {len(file_paths)} files...")

        # Generate embeddings for all files
        embeddings = {}
        valid_files = []

        for file_path in tqdm(file_paths, desc="Generating embeddings"):
            embedding = self._get_or_create_embedding(file_path, focus)
            if embedding is not None:
                embeddings[file_path] = embedding
                valid_files.append(file_path)

        if not embeddings:
            print("❌ No valid embeddings generated for indexing")
            return

        # Create embedding matrix
        self.indexed_file_paths = valid_files
        self.indexed_embeddings = embeddings
        embedding_matrix = np.vstack([embeddings[fp] for fp in valid_files]).astype(
            np.float32
        )

        # Normalize for cosine similarity
        faiss.normalize_L2(embedding_matrix)

        # Create FAISS index
        dimension = embedding_matrix.shape[1]
        self.faiss_index = faiss.IndexFlatIP(
            dimension
        )  # Inner product for cosine similarity
        self.faiss_index.add(embedding_matrix)

        print(f"✅ FAISS index built with {len(valid_files)} embeddings")

    def search_similar_with_faiss(
        self,
        target_embedding: np.ndarray,
        max_results: int = 50,
        min_similarity: float = 0.1,
    ) -> List[SimilarityResult]:
        """
        Search for similar files using FAISS index (much faster for large datasets).

        Args:
            target_embedding: Embedding of the target file
            max_results: Maximum number of results to return
            min_similarity: Minimum similarity threshold

        Returns:
            List of SimilarityResult objects sorted by similarity
        """
        if self.faiss_index is None:
            raise ValueError("FAISS index not built. Call build_faiss_index() first.")

        # Normalize target embedding
        target_embedding = target_embedding.astype(np.float32).reshape(1, -1)
        faiss.normalize_L2(target_embedding)

        # Search for similar embeddings
        similarities, indices = self.faiss_index.search(
            target_embedding, min(max_results * 2, len(self.indexed_file_paths))
        )

        # Convert to SimilarityResult objects
        results = []
        for sim, idx in zip(similarities[0], indices[0]):
            if sim >= min_similarity:
                file_path = self.indexed_file_paths[idx]
                semantic_content = self._extract_text_for_embedding(
                    file_path, "semantic"
                )
                results.append(
                    SimilarityResult(
                        file_path=file_path,
                        similarity_score=float(sim),
                        semantic_content=semantic_content[:200] + "..."
                        if len(semantic_content) > 200
                        else semantic_content,
                    )
                )

        return results[:max_results]

    def compare_yaml_to_folder(
        self,
        target_file: Path,
        folder_path: Path,
        focus: str = "semantic",
        min_similarity: float = 0.1,
        max_results: int = 50,
        use_faiss: bool = True,
        faiss_threshold: int = 100,
    ) -> List[SimilarityResult]:
        """
        Compare a single YAML file against all YAML files in a folder.

        Args:
            target_file: Path to the YAML file to compare
            folder_path: Path to folder containing YAML files to compare against
            focus: Embedding focus type ("semantic", "structural", "balanced")
            min_similarity: Minimum similarity score to include in results
            max_results: Maximum number of results to return
            use_faiss: Whether to use FAISS for large datasets (much faster)
            faiss_threshold: Use FAISS if folder has more than this many files

        Returns:
            List of SimilarityResult objects, sorted by similarity (highest first)
        """
        if not target_file.exists():
            raise FileNotFoundError(f"Target file not found: {target_file}")

        if not folder_path.exists() or not folder_path.is_dir():
            raise FileNotFoundError(f"Folder not found: {folder_path}")

        print(f"🎯 Comparing {target_file.name} against files in {folder_path}")

        # Get target file embedding
        print("🧠 Generating embedding for target file...")
        target_embedding = self._get_or_create_embedding(target_file, focus)
        if target_embedding is None:
            raise ValueError(
                f"Could not generate embedding for target file: {target_file}"
            )

        # Find all YAML files in folder
        print(f"📁 Scanning {folder_path} for YAML files...")
        yaml_files = []
        for root, _, files in os.walk(folder_path):
            for file in files:
                if file.endswith((".yaml", ".yml")):
                    file_path = Path(root) / file
                    if file_path != target_file:  # Don't compare file to itself
                        yaml_files.append(file_path)

        print(f"Found {len(yaml_files)} YAML files to compare against")

        if not yaml_files:
            return []

        # Decide whether to use FAISS based on dataset size
        use_faiss_for_search = use_faiss and len(yaml_files) >= faiss_threshold

        if use_faiss_for_search:
            print(
                f"📊 Large dataset detected ({len(yaml_files)} files). Using FAISS for efficient search..."
            )

            # Build FAISS index for all files in the folder
            self.build_faiss_index(yaml_files, focus)

            # Use FAISS for fast similarity search
            results = self.search_similar_with_faiss(
                target_embedding=target_embedding,
                max_results=max_results,
                min_similarity=min_similarity,
            )

            print(f"🚀 FAISS search completed - found {len(results)} similar files")
            return results

        else:
            print("🔍 Computing similarities using pairwise comparison...")

            # Use traditional pairwise comparison for smaller datasets
            results = []

            for file_path in tqdm(yaml_files, desc="Processing files"):
                embedding = self._get_or_create_embedding(file_path, focus)
                if embedding is None:
                    continue

                # Compute cosine similarity
                similarity = cosine_similarity([target_embedding], [embedding])[0][0]

                if similarity >= min_similarity:
                    # Get the semantic content for context
                    semantic_content = self._extract_text_for_embedding(
                        file_path, focus
                    )
                    results.append(
                        SimilarityResult(
                            file_path=file_path,
                            similarity_score=float(similarity),
                            semantic_content=semantic_content[:200] + "..."
                            if len(semantic_content) > 200
                            else semantic_content,
                        )
                    )

            # Sort by similarity (highest first) and limit results
            results.sort(key=lambda x: x.similarity_score, reverse=True)
            return results[:max_results]

    def print_similarity_report(
        self,
        target_file: Path,
        results: List[SimilarityResult],
        show_content: bool = False,
        top_n: int = 10,
    ):
        """
        Print a formatted similarity report.

        Args:
            target_file: The target file that was compared
            results: List of similarity results
            show_content: Whether to show semantic content snippets
            top_n: Number of top results to show in detail
        """
        print(f"\n📊 Similarity Report for: {target_file.name}")
        print("=" * 80)

        if not results:
            print("❌ No similar files found")
            return

        print(f"📈 Found {len(results)} similar files")
        print(f"🏆 Top similarity score: {results[0].similarity_score:.3f}")
        print(f"📉 Lowest similarity score: {results[-1].similarity_score:.3f}")

        # Statistics
        scores = [r.similarity_score for r in results]
        avg_score = sum(scores) / len(scores)
        print(f"📊 Average similarity: {avg_score:.3f}")

        # Show top N results
        print(f"\n🔝 Top {min(top_n, len(results))} most similar files:")
        print("-" * 80)

        for i, result in enumerate(results[:top_n], 1):
            print(f"{i:2d}. {result.file_path.name}")
            print(f"    📊 Similarity: {result.similarity_score:.3f}")
            print(f"    📁 Path: {result.file_path}")

            if show_content and result.semantic_content:
                print(f"    📝 Content: {result.semantic_content}")
            print()

        # Similarity distribution
        high_sim = len([r for r in results if r.similarity_score >= 0.8])
        med_sim = len([r for r in results if 0.5 <= r.similarity_score < 0.8])
        low_sim = len([r for r in results if r.similarity_score < 0.5])

        print("📈 Similarity Distribution:")
        print(f"   🟢 High (≥0.8): {high_sim} files")
        print(f"   🟡 Medium (0.5-0.8): {med_sim} files")
        print(f"   🔴 Low (<0.5): {low_sim} files")


def main():
    """Main function with command line interface."""
    parser = argparse.ArgumentParser(
        description="Compare a YAML file against a folder of YAML files for similarity",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Compare a single file against a folder
  python yaml_similarity_scorer.py target.yaml /path/to/yaml/folder
  
  # Use structural focus and show top 20 results
  python yaml_similarity_scorer.py target.yaml /path/to/folder --focus structural --top-n 20
  
  # Show content snippets and use higher similarity threshold
  python yaml_similarity_scorer.py target.yaml /path/to/folder --show-content --min-similarity 0.3
        """,
    )

    parser.add_argument("target_file", help="YAML file to compare")
    parser.add_argument(
        "folder_path", help="Folder containing YAML files to compare against"
    )
    parser.add_argument(
        "--focus",
        choices=["semantic", "structural", "balanced"],
        default="semantic",
        help="Embedding focus type (default: semantic)",
    )
    parser.add_argument(
        "--min-similarity",
        type=float,
        default=0.1,
        help="Minimum similarity score to include (default: 0.1)",
    )
    parser.add_argument(
        "--max-results",
        type=int,
        default=50,
        help="Maximum number of results to return (default: 50)",
    )
    parser.add_argument(
        "--top-n",
        type=int,
        default=10,
        help="Number of top results to show in detail (default: 10)",
    )
    parser.add_argument(
        "--show-content",
        action="store_true",
        help="Show content snippets in the report",
    )
    parser.add_argument(
        "--cache-dir",
        default=".yaml_similarity_cache",
        help="Cache directory for embeddings (default: .yaml_similarity_cache)",
    )
    parser.add_argument(
        "--use-gpu", action="store_true", help="Use GPU acceleration if available"
    )
    parser.add_argument(
        "--no-faiss",
        action="store_true",
        help="Disable FAISS indexing (use pairwise comparison)",
    )
    parser.add_argument(
        "--faiss-threshold",
        type=int,
        default=100,
        help="Use FAISS if folder has more than this many files (default: 100)",
    )

    args = parser.parse_args()

    # Validate inputs
    target_file = Path(args.target_file)
    folder_path = Path(args.folder_path)

    if not target_file.exists():
        print(f"❌ Error: Target file not found: {target_file}")
        return 1

    if not folder_path.exists() or not folder_path.is_dir():
        print(f"❌ Error: Folder not found: {folder_path}")
        return 1

    try:
        # Initialize scorer
        scorer = YAMLSimilarityScorer(cache_dir=args.cache_dir, use_gpu=args.use_gpu)

        # Perform comparison
        start_time = time.time()
        results = scorer.compare_yaml_to_folder(
            target_file=target_file,
            folder_path=folder_path,
            focus=args.focus,
            min_similarity=args.min_similarity,
            max_results=args.max_results,
            use_faiss=not args.no_faiss,
            faiss_threshold=args.faiss_threshold,
        )
        elapsed_time = time.time() - start_time

        # Print report
        scorer.print_similarity_report(
            target_file=target_file,
            results=results,
            show_content=args.show_content,
            top_n=args.top_n,
        )

        print(f"\n⏱️  Processing completed in {elapsed_time:.1f} seconds")

        return 0

    except Exception as e:
        print(f"❌ Error: {e}")
        return 1


if __name__ == "__main__":
    exit(main())
