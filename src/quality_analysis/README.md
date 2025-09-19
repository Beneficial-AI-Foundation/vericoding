# Quality Analysis Tools

Code quality analysis for Verus, Dafny, and Lean benchmarks.

## Structure

```
quality_analysis/
├── add_qa_metadata.py         # Main tool: adds QA metadata to JSONL files
├── analyze_all.py             # Run all analysis tools
├── *_similarity.py            # Similarity detection tools
├── config/                    # Configuration files
│   ├── qa_config.yaml         # Default configuration
│   ├── fast_config.yaml       # Fast/lenient settings
│   └── high_quality_config.yaml # Strict settings
├── verus/                     # Verus analysis tools
├── dafny/                     # Dafny analysis tools
└── lean/                      # Lean analysis tools
```

## Usage

### Generate QA Metadata
```bash
# Basic usage
python3 add_qa_metadata.py benchmarks/verus/numpy_triple

# With output
python3 add_qa_metadata.py --output-metadata summary benchmarks

# Custom configuration
python3 add_qa_metadata.py --config config/fast_config.yaml benchmarks
```

### Programmatic Usage
```python
from add_qa_metadata import get_qa_metadata

metadata = get_qa_metadata("benchmarks/verus/numpy_triple")
print(f"Score: {metadata['score']}")
```

## Quality Scoring

Score = max(0, base_score - penalties)

**Base Score Modes:**
- `fixed`: Constant 100
- `proportional`: entries × 0.5 (default, capped 50-500)
- `logarithmic`: 50 × log(entries + 1)

**Penalties (default):**
- Verus: specs_defaults×5 + exec_bodies×12 + ghost_types×0.5 + duplicates×2
- Dafny: func_defaults×5 + method_bodies×12 + duplicates×2  
- Lean: sorry×12 + duplicates×2

## Configuration

Edit `config/qa_config.yaml` to adjust:
- Base score calculation mode
- Penalty weights per issue type
- Similarity detection settings
- Performance parameters

**Presets:**
- `config/fast_config.yaml`: Lenient penalties for development
- `config/high_quality_config.yaml`: Strict penalties for production

## Individual Tools

### Verus
- `check_spec_functions.py`: Find default values in spec functions
- `check_verus_functions.py`: Find implementations in exec functions
- `check_verus_types.py`: Find ghost types in exec functions

### Dafny
- `check_dafny_functions.py`: Find default values in functions/predicates
- `check_dafny_methods.py`: Find implementations in methods
- `check_dafny_yaml.py`: Analyze YAML files

### Lean
- `check_lean_definitions.py`: Find sorry usage in definitions

All tools support:
- Single files: `script.py path/to/file.ext`
- Directories: `script.py path/to/directory/`
- JSON output: `--output json`
- Quiet mode: `--quiet`

## Run All Tools
```bash
python3 analyze_all.py benchmarks
```