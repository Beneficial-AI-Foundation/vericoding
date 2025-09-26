# A Benchmark For Vericoding: Formally Verified Program Synthesis

Our paper (currently undergoing review) can be found on [ArXiv]().

Our scripts can be found in this [GitHub repo](https://github.com/beneficial-AI-Foundation/vericoding).

The `vericoding_benchmark_v1.csv` provides a list of Vericoding IDs, sources and the source IDs for all 12,504 tasks. It also contains additional metadata from our quality analysis.

The file `vericoding_results_v1.csv` which is a list of the outcomes of all 55,397 experiments involving vericoding tasks across different models.

## Specs

The folder `specs` contains all 12,504 tasks in Dafny, Lean and Verus, which includes the following.

* Files which compile, up to some `sorry` or `assume false` in the code. The file is decomposed into different components, such as the preamble, the spec, the code and the postamble.

* Files which do not compile, especially after translation from another langauge. We keep them in the benchmark for researchers who want use them for other experiments, e.g. spec repair.

## JSONL

The folder `jsonl` contains the tasks and issues sorted into the different languages, parsed into different components, and stored as JSON lines for easier experimentation.

## Vericoded

The folder `vericoded` will contain some of the tasks with solutions filled in by an AI vericoder.

## Humancoded

The folder `humancoded` will contain some of the tasks with solutions filled in by human coders.

## Original Sources

### DafnyBench
* `benchmarks/dafny/dafnybench`
* https://github.com/sun-wendy/DafnyBench

### NumPyTriple
* `benchmarks/lean/numpy_triple`
* Derived from NumPy documentation
* Specs in new Hoare triple format

### NumPySimple
* `benchmarks/lean/numpy_simple`
* Derived from NumPy documentation
* Specs in classical Lean format

### Verina
* `benchmarks/lean/verina`
* https://github.com/sunblaze-ucb/verina

### APPS
* `benchmarks/dafny/apps`
* https://github.com/hendrycks/apps

### FVAPPS
* `benchmarks/lean/fvapps`
* https://huggingface.co/datasets/quinn-dougherty/fvapps

### VerifiedCogen
* `benchmarks/verus/verified_cogen`
* https://github.com/JetBrains-Research/verified-cogen

### BigNum
* `benchmarks/dafny/bignum`
* Written from scratch

### HumanEval, Clever
* `benchmarks/dafny/humaneval`
* `benchmarks/lean/clever`
* https://github.com/openai/human-eval
* https://github.com/JetBrains-Research/HumanEval-Dafny
* https://github.com/trishullab/clever

The Dafny files were mostly translated from the original Python source. Some of the Dafny files were taken from Jetbrains Research's HumanEval Dafny repo.

The Lean files were taken from the Clever benchmark which were originally derived from the HumanEval benchmark. HumanEval problems 22, 137, 162 are missing from Clever for reasons mentioned in the Clever paper.