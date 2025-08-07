# Code2Verus

A multi-language translator extending [Quinn's dafny2verus](https://github.com/Beneficial-AI-Foundation/dafny2verus) for converting formal verification code to [Verus](https://verus-lang.github.io/verus/guide/overview.html) using `PydanticAI`.

## Supported Languages

- **Dafny**: Translate from Dafny verification language to Verus
- **Lean 4**: Translate from Lean 4 theorem prover to Verus

## Features

- Preserves formal semantics, contracts, and proof structures
- Language-specific translation prompts for optimal results
- Concurrent processing for batch translations
- Support for various benchmarks including [DafnyBench](https://huggingface.co/datasets/wendy-sun/DafnyBench)

## Usage

```bash
# Translate Dafny code (default)
uv run code2verus

# Translate Dafny code explicitly
uv run code2verus --language dafny

# Translate Lean 4 code
uv run code2verus --language lean --benchmark your-lean-benchmark

# Use specific dataset and split
uv run code2verus --benchmark wendy-sun/DafnyBench --split test --language dafny

# Increase concurrent translations
uv run code2verus --max-concurrent 5
```

## Command Line Options

- `--benchmark`: Hugging Face dataset path (default: wendy-sun/DafnyBench)
- `--split`: Dataset split to use (default: test)
- `--language`: Source language - either "dafny" or "lean" (default: dafny)
- `--max-concurrent`: Maximum number of concurrent translations (default: 3)
