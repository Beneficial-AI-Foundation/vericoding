# Experiments analysis and visualization

## 1. Fetch run data from wandb using `wandb_pull_run_files.py`

Make sure `WANDB_API_KEY` is set in your environment, then run

```console
uv run scripts/wandb_pull_run_files.py --run https://wandb.ai/vericoding/vericoding/runs/<ID>
```

This should create a `wandb_exports` folder and an `<ID>` subfolder within it, containing run data. For more variations, use `--help` with `wandb_pull_run_files`.

## 2. Create an analysis file using `analyze_wandb_runs.py`

Run 

```console
uv run scripts/analyze_wandb_runs.py --rundir wandb_exports/<ID>        
```

This should create `analysis.json` in `wandb_exports/<ID>`. For more variations, use `--help` with `analyze_wandb_runs`.

## 3. Create a plot using `make_plot.py`

Run

```console
uv run scripts/make_plot.py --rundir wandb_exports/<ID> --buckets N
```

This should create `plot.pdf` in `wandb_exports/<ID>`. For more variations, use `--help` with `make_plot`.
