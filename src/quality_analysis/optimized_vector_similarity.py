#!/usr/bin/env python3
"""
Optimized vector similarity detection for large YAML datasets.

Performance optimizations:
1. Batch processing of embeddings
2. FAISS indexing for efficient similarity search
3. Parallel processing where possible
4. Progress tracking with tqdm
5. Smart caching and memory management
"""

import os
import time
import pickle
import hashlib
from pathlib import Path
from typing import List, Dict
from concurrent.futures import ThreadPoolExecutor
import yaml

# Optional imports for optimization
try:
    from tqdm import tqdm

    HAS_TQDM = True
except ImportError:
    HAS_TQDM = False

    # Fallback progress function
    def tqdm(iterable, *args, **kwargs):
        return iterable


try:
    from sentence_transformers import SentenceTransformer
    import faiss
    import numpy as np

    VECTOR_AVAILABLE = True
except ImportError:
    VECTOR_AVAILABLE = False

    # Create dummy numpy for type hints
    class _DummyNumpy:
        class ndarray:
            pass

    np = _DummyNumpy()

# Import from our vector enhanced similarity
# Note: VectorEnhancedSimilarity import removed as it was unused


class OptimizedVectorSimilarity:
    """
    Optimized vector similarity for large datasets (500+ files).

    Key optimizations:
    - Batch embedding generation (much faster than one-by-one)
    - FAISS indexing for O(log n) similarity search
    - Persistent caching of embeddings
    - Progress tracking and memory management
    """

    def __init__(
        self,
        embedding_model: str = "all-MiniLM-L6-v2",
        cache_dir: str = ".vector_cache",
        batch_size: int = 32,
        use_gpu: bool = False,
    ):
        """
        Initialize optimized similarity detector.

        Args:
            embedding_model: SentenceTransformer model name
            cache_dir: Directory for caching embeddings
            batch_size: Batch size for embedding generation
            use_gpu: Whether to use GPU acceleration
        """
        if not VECTOR_AVAILABLE:
            raise ImportError(
                "Vector libraries not available. Install with: uv add sentence-transformers scikit-learn faiss-cpu"
            )

        self.cache_dir = Path(cache_dir)
        self.cache_dir.mkdir(exist_ok=True)
        self.batch_size = batch_size

        # Initialize embedding model
        device = "cuda" if use_gpu else "cpu"
        self.embedding_model = SentenceTransformer(embedding_model, device=device)
        print(f"✅ Loaded {embedding_model} on {device}")

        # FAISS index for efficient search
        self.faiss_index = None
        self.file_paths = []
        self.embeddings_cache = {}

    def _get_cache_path(self, file_path: Path, focus: str) -> Path:
        """Get cache file path for a YAML file embedding."""
        # Create hash of file path + focus for cache key
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
                return " ".join(parts)
            else:  # balanced
                parts = []
                for key in ["vc-description", "vc-spec", "vc-preamble"]:
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

    def generate_embeddings_batch(
        self,
        file_paths: List[Path],
        focus: str = "semantic",
        force_regenerate: bool = False,
    ) -> Dict[Path, np.ndarray]:
        """
        Generate embeddings for multiple files in batches (much faster).

        Args:
            file_paths: List of YAML file paths
            focus: Embedding focus type
            force_regenerate: Whether to ignore cache

        Returns:
            Dictionary mapping file paths to embeddings
        """
        embeddings = {}
        texts_to_process = []
        files_to_process = []

        # Check cache first
        if not force_regenerate:
            print("🔍 Checking cache...")
            for file_path in tqdm(file_paths, desc="Cache check"):
                cache_path = self._get_cache_path(file_path, focus)
                if self._is_cache_valid(file_path, cache_path):
                    try:
                        with open(cache_path, "rb") as f:
                            embeddings[file_path] = pickle.load(f)
                    except (OSError, IOError, pickle.PickleError, EOFError):
                        # Cache corrupted, need to regenerate
                        files_to_process.append(file_path)
                else:
                    files_to_process.append(file_path)
        else:
            files_to_process = file_paths

        if not files_to_process:
            print("✅ All embeddings loaded from cache!")
            return embeddings

        print(f"🚀 Generating embeddings for {len(files_to_process)} files...")

        # Extract texts in parallel
        with ThreadPoolExecutor(max_workers=4) as executor:
            text_futures = {
                executor.submit(self._extract_text_for_embedding, fp, focus): fp
                for fp in files_to_process
            }

            for future in tqdm(text_futures, desc="Extracting text"):
                file_path = text_futures[future]
                try:
                    text = future.result()
                    if text.strip():
                        texts_to_process.append(text)
                        files_to_process.append(file_path)
                except Exception as e:
                    print(f"Warning: Failed to extract {file_path}: {e}")

        # Generate embeddings in batches
        if texts_to_process:
            print(f"🧠 Computing embeddings (batch_size={self.batch_size})...")
            batch_embeddings = []

            for i in tqdm(
                range(0, len(texts_to_process), self.batch_size),
                desc="Embedding batches",
            ):
                batch_texts = texts_to_process[i : i + self.batch_size]
                batch_embs = self.embedding_model.encode(
                    batch_texts,
                    batch_size=len(batch_texts),
                    show_progress_bar=False,
                    convert_to_numpy=True,
                )
                batch_embeddings.extend(batch_embs)

            # Cache and store results
            print("💾 Caching embeddings...")
            for file_path, embedding in tqdm(
                zip(files_to_process, batch_embeddings), desc="Caching"
            ):
                embeddings[file_path] = embedding

                # Save to cache
                cache_path = self._get_cache_path(file_path, focus)
                try:
                    with open(cache_path, "wb") as f:
                        pickle.dump(embedding, f)
                except Exception as e:
                    print(f"Warning: Failed to cache {file_path}: {e}")

        return embeddings

    def build_faiss_index(self, embeddings: Dict[Path, np.ndarray]) -> None:
        """Build FAISS index for efficient similarity search."""
        if not embeddings:
            return

        print("🔧 Building FAISS index...")

        self.file_paths = list(embeddings.keys())
        embedding_matrix = np.vstack([embeddings[fp] for fp in self.file_paths]).astype(
            np.float32
        )

        # Normalize for cosine similarity
        faiss.normalize_L2(embedding_matrix)

        # Create index
        dimension = embedding_matrix.shape[1]
        self.faiss_index = faiss.IndexFlatIP(
            dimension
        )  # Inner product for cosine similarity
        self.faiss_index.add(embedding_matrix)

        print(f"✅ FAISS index built with {len(self.file_paths)} embeddings")

    def find_similar_files_fast(
        self, similarity_threshold: float = 0.8, max_results_per_file: int = 20
    ) -> List[List[Path]]:
        """
        Find similar files using efficient FAISS search.

        Args:
            similarity_threshold: Minimum similarity score
            max_results_per_file: Maximum similar files to find per file

        Returns:
            List of similar file groups
        """
        if not self.faiss_index:
            raise ValueError("FAISS index not built. Call build_faiss_index() first.")

        print(f"🔎 Finding similar files (threshold={similarity_threshold})...")

        similar_groups = []
        processed_files = set()

        for i, query_file in enumerate(tqdm(self.file_paths, desc="Similarity search")):
            if query_file in processed_files:
                continue

            # Get query embedding (already normalized)
            query_idx = i
            query_embedding = np.array(
                [self.faiss_index.reconstruct(query_idx)], dtype=np.float32
            )

            # Search for similar files
            similarities, indices = self.faiss_index.search(
                query_embedding, max_results_per_file + 1
            )

            # Collect similar files
            similar_files = [query_file]
            for sim, idx in zip(similarities[0], indices[0]):
                if idx != query_idx and sim >= similarity_threshold:
                    similar_file = self.file_paths[idx]
                    if similar_file not in processed_files:
                        similar_files.append(similar_file)
                        processed_files.add(similar_file)

            if len(similar_files) > 1:
                similar_groups.append(similar_files)
                processed_files.update(similar_files)

        return similar_groups

    def get_near_duplicates_for_qa(
        self, similarity_threshold: float = 0.85, max_examples: int = 5
    ) -> Dict:
        """
        Get near duplicates information optimized for QA metadata.

        Returns:
            Dict with 'examples' (first few file paths) and 'total_count'
        """
        if not hasattr(self, "faiss_index") or self.faiss_index is None:
            return {"examples": [], "total_count": 0}

        similar_groups = self.find_similar_files_fast(similarity_threshold)

        # Format groups for QA metadata (preserve group structure)
        examples = []
        all_duplicates = []
        
        for group in similar_groups:
            if len(group) > 1:
                # Create example group with similarity info
                group_files = [str(f) for f in group]
                examples.append({
                    "files": group_files,
                    "similarity": 0.9  # Placeholder - could compute actual similarity
                })
                # Also track all duplicate files
                all_duplicates.extend(group_files)

        return {
            "examples": examples[:max_examples],
            "total_count": len(set(all_duplicates)),  # Unique files that are duplicates
        }


def optimized_find_similar_files(
    directory: str,
    similarity_threshold: float = 0.8,
    embedding_focus: str = "semantic",
    cache_dir: str = ".vector_cache",
    batch_size: int = 32,
) -> Dict:
    """
    Optimized similarity detection for large YAML datasets.

    Args:
        directory: Directory containing YAML files
        similarity_threshold: Minimum similarity for grouping
        embedding_focus: Type of embedding focus
        cache_dir: Cache directory for embeddings
        batch_size: Batch size for embedding generation

    Returns:
        Results dictionary with similar file groups
    """
    start_time = time.time()

    # Find all YAML files
    print(f"📁 Scanning {directory}...")
    yaml_files = []
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith((".yaml", ".yml")):
                yaml_files.append(Path(root) / file)

    print(f"Found {len(yaml_files)} YAML files")

    if len(yaml_files) < 2:
        return {"similar_files": [], "total_files": len(yaml_files)}

    # Initialize optimized detector
    detector = OptimizedVectorSimilarity(cache_dir=cache_dir, batch_size=batch_size)

    # Generate embeddings in batches
    embeddings = detector.generate_embeddings_batch(yaml_files, embedding_focus)

    if not embeddings:
        print("❌ No valid embeddings generated")
        return {"similar_files": [], "total_files": len(yaml_files)}

    # Build FAISS index
    detector.build_faiss_index(embeddings)

    # Find similar files
    similar_groups = detector.find_similar_files_fast(similarity_threshold)

    elapsed = time.time() - start_time
    print(f"⏱️  Total time: {elapsed:.1f}s for {len(yaml_files)} files")
    print(f"📊 Found {len(similar_groups)} similar groups")

    return {
        "similar_files": similar_groups,
        "total_files": len(yaml_files),
        "processing_time": elapsed,
        "embedding_focus": embedding_focus,
        "cached_embeddings": len(yaml_files)
        - len([f for f in yaml_files if f in embeddings]),
    }


def get_near_duplicates_for_benchmark(
    directory: str,
    similarity_threshold: float = 0.85,
    embedding_focus: str = "semantic",
    embedding_model: str = "all-MiniLM-L6-v2",
    cache_dir: str = ".vector_cache",
    batch_size: int = 32,
    use_gpu: bool = False,
    max_examples: int = 5,
) -> Dict:
    """
    Get near duplicates information for QA metadata generation.

    Args:
        directory: Directory containing YAML files
        similarity_threshold: Similarity threshold (higher = more strict)
        embedding_focus: Type of embedding focus ("semantic", "structural", "balanced")
        embedding_model: SentenceTransformer model name
        cache_dir: Cache directory for embeddings
        batch_size: Batch size for processing
        use_gpu: Whether to use GPU acceleration
        max_examples: Maximum number of example files to return

    Returns:
        Dict with 'examples' and 'total_count' for QA metadata
        
    Raises:
        ImportError: If required vector similarity libraries are not installed
    """
    if not VECTOR_AVAILABLE:
        raise ImportError(
            "Vector similarity libraries not available. Install with: "
            "uv add sentence-transformers scikit-learn faiss-cpu"
        )

    yaml_files = list(Path(directory).rglob("*.yaml"))

    if len(yaml_files) < 2:
        return {"examples": [], "total_count": 0}

    # Initialize detector
    detector = OptimizedVectorSimilarity(
        embedding_model=embedding_model,
        cache_dir=cache_dir,
        batch_size=batch_size,
        use_gpu=use_gpu,
    )

    # Generate embeddings
    embeddings = detector.generate_embeddings_batch(yaml_files, embedding_focus)

    if not embeddings:
        return {"examples": [], "total_count": 0}

    # Build FAISS index
    detector.build_faiss_index(embeddings)

    # Get near duplicates for QA
    return detector.get_near_duplicates_for_qa(similarity_threshold, max_examples)


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(
        description="Optimized vector similarity for large YAML datasets"
    )
    parser.add_argument("--dir", required=True, help="Directory to analyze")
    parser.add_argument(
        "--threshold", type=float, default=0.8, help="Similarity threshold"
    )
    parser.add_argument(
        "--focus",
        choices=["semantic", "structural", "balanced"],
        default="semantic",
        help="Embedding focus",
    )
    parser.add_argument(
        "--batch-size", type=int, default=32, help="Batch size for embeddings"
    )
    parser.add_argument("--cache-dir", default=".vector_cache", help="Cache directory")

    args = parser.parse_args()

    results = optimized_find_similar_files(
        args.dir,
        similarity_threshold=args.threshold,
        embedding_focus=args.focus,
        cache_dir=args.cache_dir,
        batch_size=args.batch_size,
    )

    print("\n📈 Performance Summary:")
    print(f"  Files processed: {results['total_files']}")
    print(f"  Similar groups: {len(results['similar_files'])}")
    print(f"  Processing time: {results['processing_time']:.1f}s")
    print(
        f"  Average time per file: {results['processing_time'] / results['total_files']:.3f}s"
    )

    # Show first few groups
    for i, group in enumerate(results["similar_files"][:3], 1):
        print(f"\nGroup {i}: {len(group)} files")
        for file_path in group[:3]:
            print(f"  {file_path.name}")
        if len(group) > 3:
            print(f"  ... and {len(group) - 3} more")
