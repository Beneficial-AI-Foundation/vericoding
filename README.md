# A Benchmark For Vericoding: Formally Verified Program Synthesis

Paper currently under ICLR review. 

Disclaimer: some of the scripts may not run because they are stripped down versions of our original scripts to anonymize them. We will provide the full scripts on GitHub after the paper is accepted. 

## Benchmarks
The `benchmarks` folder contains our three benchmarks in Dafny, Verus and Lean.

* Each language folder contains a `tasks` folder with specs which compile, up to some `sorry` or `assume false` in the code. There is also an `issues` folder with specs which do not compile. We keep them in the benchmark for researchers who want to fix them or use them for other experiments.

* There are two files `lean_tasks.jsonl` and `lean_issues.jsonl` which contain each task as a JSON line. The task is decomposed into different components, such as the preamble, spec and code. We also provide additional metadata from our quality analysis. We have similar files for Dafny and for Verus.

* The `README.md` file lists the original sources used in constructing these benchmarks, with download links. The `vericoding_benchmark_v1.csv` provides a list of Vericoding IDs and the source IDs for all 12,504 tasks. The information is also available in JSONL format: `verucoding_benchmark_v1.jsonl`.

## Experiments

The experiments folder contains `vericoding_results_v1.csv` which is a list of the outcomes of all 55397 experiments involving vericoding tasks across different models.

## Source code

The `src` folder contains scripts that we used during the construction of this benchmark, such as translation, formatting and quality analysis. It also contains scripts for running the vericoding experiments.

