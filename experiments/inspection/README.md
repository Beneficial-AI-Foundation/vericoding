# METHODOLOGY

In order to inspect the vericoding process' validity, we perform manual inspection on a selection of vericoding tasks. For each language considered, and each benchmark collected from, or transpiled to, the chosen language, we perform the following steps:

1. Pick 5 vericoding outputs uniformly at random from `benchmarks/<LANG>/<BENCH>/vericoding-results/success`
1. For each output selected in this way, we fill out the `analysis_template.yaml`, making notes of AI behavior that could be considered as cheating (either in the vericoding step, or, if the benchmark set was transpiled, also in the transpilation step). Examples of cheating include, but aren't limited to:
    - Using `sorry`, `assume(false)` or similar
    - Removing postconditions of functions in the original problem (e.g. `ensures true` instead of the original property)
    - Using analysis-circumventing annotations (e.g. `#[verifier::external]` in Verus) 

We can automate step 1, by calling
```console
uv run scripts/pick_random.py --lang <LANG> --bench <BENCH> --n <N>
```
from the repo root.

For the lean runs the output files weren't located in the same way so the script couldn't be used. Instead, repeating 5 times for each bench:
- randomly choose an llm with at least one success
- Open the wandb page, navigate to table 3, filter for success, randomly choose one of these files
- copy the output file to lean-enabled IDE and check
