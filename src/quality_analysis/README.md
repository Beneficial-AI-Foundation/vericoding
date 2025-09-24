# Quality Analysis Tools

Code quality analysis for Verus, Dafny, and Lean benchmarks with dual-level scoring.

## Overview

Generates **two types** of quality analysis:
1. **Benchmark-level metadata**: Overall quality scores in separate `.metadata.json` files  
2. **Per-entry scoring**: Individual quality scores in enhanced `_with_entry_qa.jsonl` files

## Output Structure

```
benchmarks/verus/humaneval/
├── verus_humaneval.jsonl                    # Original entries (unchanged)
├── verus_humaneval.metadata.json            # Benchmark-level metadata
├── verus_humaneval_with_entry_qa.jsonl      # Enhanced with per-entry scores
└── yaml/, files/                            # Source files
```

## Usage

### Generate Quality Analysis
```bash
# Process single benchmark - generates BOTH metadata and enhanced JSONL
python3 add_qa_metadata.py benchmarks/verus/humaneval

# Process all benchmarks
python3 add_qa_metadata.py benchmarks

# Show summary
python3 add_qa_metadata.py --output-metadata summary benchmarks
```

### Programmatic Access
```python
from add_qa_metadata import load_benchmark_with_metadata, get_benchmark_quality_score

# Load entries with per-entry scores
entries, metadata = load_benchmark_with_metadata("benchmarks/verus/humaneval/verus_humaneval.jsonl")

# Get benchmark quality score
score = get_benchmark_quality_score("benchmarks/verus/humaneval/verus_humaneval.jsonl")
```

## Quality Scoring

**Normalized scoring for cross-benchmark comparison:**

### Benchmark-Level Formula (NEW)
```
final_score = 100 × (1 - penalty_fraction)  [0-100 scale]
penalty_fraction = Σ(weight_i × proportion_i)
proportion_i = issue_count_i / total_entries
```

**Score Interpretation:**
- **90-100**: Excellent quality (minimal issues)
- **70-89**: Good quality (some issues)  
- **50-69**: Moderate quality (notable issues)
- **30-49**: Poor quality (significant issues)
- **0-29**: Very poor quality (critical issues)

### Per-Entry Formula  
```
individual_score = 1 - Σ(weight_i × p_i)  [0-1 scale]
p_i = 1 if entry has issue_i, else 0
```

**Key Benefits:**
- **Cross-benchmark comparable**: Same scale regardless of benchmark size
- **Size-independent**: 100 entries vs 1000 entries both use 0-100 scale
- **Intuitive**: Percentage-like scoring that's easy to interpret

### Quality Factors & Weights
- **Verus**: specs with defaults (30%), exec bodies (50%), ghost types (5%), near-duplicates (15%)
- **Dafny**: func defaults (40%), method bodies (45%), near-duplicates (15%)  
- **Lean**: sorry usage (85%), near-duplicates (15%)

### Real Examples (with normalized scoring)
```
dafny_bignum (62 entries):     85.2/100 - Good quality, high duplication penalty
lean_bignum (62 entries):     18.3/100 - Poor quality, many sorry definitions  
verus_apps (536 entries):     99.4/100 - Excellent quality, minimal issues
lean_apps (676 entries):      99.6/100 - Excellent quality, very few issues
```

**Note**: All scores directly comparable regardless of benchmark size!

### Example Per-Entry Output
```json
{
  "id": "VH0000",
  "source_id": "humaneval_000",
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
```

## Dependencies

**Required for near-duplicate detection:**
```bash
uv add sentence-transformers scikit-learn faiss-cpu
```

## Configuration

Edit `config/qa_config.yaml` to adjust weights, similarity thresholds, and performance settings.

**Key settings:**
```yaml
scoring:
  use_normalized_quality: true              # Enable 0-100 scale scoring
  
  verus:
    weights:                                    # Must sum to 1.0
      specs_with_default_values_weight: 0.30   # 30%
      execs_with_bodies_weight: 0.30           # 30% 
      execs_with_ghost_types_weight: 0.25      # 25%
      near_duplicates_weight: 0.15             # 15%
```

## Individual Analysis Tools

- **Verus**: `check_spec_functions.py`, `check_verus_functions.py`, `check_verus_types.py`
- **Dafny**: `check_dafny_functions.py`, `check_dafny_methods.py`  
- **Lean**: `check_lean_definitions.py`

All support single files, directories, JSON output (`--output json`), and quiet mode (`--quiet`).