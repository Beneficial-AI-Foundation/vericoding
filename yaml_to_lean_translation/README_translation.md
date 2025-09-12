# YAML to Lean Translation Script

This script translates Dafny YAML specifications to Lean 4 using the Claude API.

## Setup

1. **Install dependencies:**

   ```bash
   pip install -r requirements_translation.txt
   ```

2. **Set your Claude API key:**
   ```bash
   export CLAUDE_API_KEY='your-api-key-here'
   ```

## Usage

### Test with a single file

```bash
python test_translation.py
```

### Translate all 443 files

```bash
python translate_yaml_to_lean.py --api-key $CLAUDE_API_KEY
```

### Translate with a limit (for testing)

```bash
python translate_yaml_to_lean.py --api-key $CLAUDE_API_KEY --limit 5
```

### Use a different Claude model

```bash
python translate_yaml_to_lean.py --api-key $CLAUDE_API_KEY --model claude-3-opus-20240229
```

## Features

- **Batch processing**: Translates all 443 YAML files automatically
- **Error handling**: Retries failed API calls with exponential backoff
- **Progress tracking**: Shows progress and success rate
- **Rate limiting**: Respects API limits with 1-second delays
- **Comprehensive translation**: Converts Dafny syntax to Lean 4 syntax
- **Proper structure**: Creates well-organized Lean files with imports and documentation

## Output

Translated Lean files are saved to a single folder:

```
benchmarks/vericoding_lean/yaml-depsontop-translated/
```

All 443 translated Lean files will be in this single directory with cleaned filenames.

## Translation Guidelines

The script translates:

- Dafny types to Lean types (`int` → `Int`, `seq<T>` → `List T`, etc.)
- Dafny syntax to Lean syntax (`forall` → `∀`, `==>` → `→`, etc.)
- Method specifications to Lean theorems with Hoare triples
- Array access patterns (`a[i]` → `a[i]!`)
- Quantifiers and logical operators

## Cost Estimation

With 443 files and approximately 1 API call per file:

- **Claude 3 Sonnet**: ~$0.15 per 1K tokens input, ~$0.60 per 1K tokens output
- **Estimated total cost**: $50-200 depending on file complexity

## Troubleshooting

- **API key issues**: Make sure your Claude API key is valid and has sufficient credits
- **Rate limiting**: The script includes delays, but you may need to adjust for your API tier
- **File errors**: Check the error log for specific file issues
- **Memory issues**: Process files in smaller batches using the `--limit` option

## Example Output

The script will create Lean files like:

```lean
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "PowerOfListElements",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification",
  "source": "Dafny",
  "translation_date": "2024"
}
-//

namespace DafnyBenchmarks

/-- PowerOfListElements: Automatically translated from Dafny specification -/

def Power (base : Int) (exponent : Int) : Int :=
  if exponent ≥ 0 then
    if exponent = 0 then 1
    else base * Power base (exponent - 1)
  else sorry

theorem PowerOfListElements_spec (l : List Int) (n : Int) :
    ⦃⌜n ≥ 0⌝⦄
    PowerOfListElements l n
    ⦃⇓result => ⌜result.length = l.length ∧
                 ∀ i : Fin l.length, result.get i = Power (l.get i) n⌝⦄ := by
  sorry

end DafnyBenchmarks
```
