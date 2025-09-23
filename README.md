# A Benchmark For Vericoding: Formally Verified Program Synthesis

Paper currently under ICLR review. 

Disclaimer: some of the scripts may not run because they are stripped down versions of our original scripts to anonymize them. We will provide the full scripts on GitHub after the paper is accepted. 

## Benchmarks
The `benchmarks` folder contains our three benchmarks in Dafny, Verus and Lean.

* Each language folder contains a `tasks` folder with specs which compile, up to some `sorry` or `assume false` in the code. There is also an `issues` folder with specs which do not compile. We keep them in the benchmark for researchers who want to fix them or use them for other experiments.

* There are two files `lean_tasks.jsonl` and `lean_issues.jsonl` which contain each task as a JSON line. The task is decomposed into different components, such as the preamble, spec and code. We also provide additional metadata from our quality analysis. This data is also available as CSV files.

* The `README.md` file lists the original sources used in constructing these benchmarks, with download links. The `tasks_metadata.json` provides a dictionary between our Vericoding IDs and the source IDs of each task.

## Source code

The `src` folder contains scripts that we used during the construction of this benchmark, such as translation, formatting and quality analysis. It also contains scripts for running the vericoding experiments.

