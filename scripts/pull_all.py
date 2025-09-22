import json
import pathlib
import csv
import argparse
from pathlib import Path

import subprocess

RUN_URL_BASE = "https://wandb.ai/vericoding/vericoding/runs/"

THIS_DIR = pathlib.Path(__file__).parent.resolve()

REPO = THIS_DIR.parent

DEFAULT_EXPORTS = REPO / "wandb_exports"

FIELDNAMES = ["Language", "LLM", "Benchmark", "WandB ID", "Task ID", "Success", "Specification length", "Solution length", "Spec ratio"]
FIELDNAMES_TASKS = ["Task ID", "Task"]

RUN_JSON_PATH = REPO / "experiments" / "wandb_runs.json"

LANG = {
    "dafny": "D",
    "lean": "L",
    "verus": "V"
}

BENCH = {
    "numpy-simple": "S",
    "numpy-triple": "T",
    "dafnybench": "D",
    "humaneval": "H",
    "verina": "V",
    "bignum": "B",
    "verified-cogen": "G",
    "apps": "A"

}

def idLabel(lang: str, bench: str, taskId: int) -> str:
    return f"{LANG[lang]}{BENCH[bench]}{taskId:04}"

def main() -> None:
    p = argparse.ArgumentParser(description="Collect run statistics")
    p.add_argument("--root", default=None, help="Output directory root (default: wandb_exports)")
    p.add_argument("--overwrite", action="store_true", help="Overwrite files if they already exist")
    p.add_argument("--debug", action="store_true", help="Echo all subcalls instead")

    args = p.parse_args()

    EXPORTS = Path(args.root or DEFAULT_EXPORTS)
    EXPORTS.mkdir(parents=True, exist_ok=True)

    CSV = EXPORTS / "aggregate.csv"

    TASKS = EXPORTS / "tasks.csv"

    SKIPPED = EXPORTS / "skipped.txt"

    allRuns = None
    with open(RUN_JSON_PATH, "r") as f:
        allRuns = json.loads(f.read())

    with open(CSV, 'w', newline='') as outcsv:
        writer = csv.DictWriter(outcsv, fieldnames=FIELDNAMES)
        writer.writeheader()
    
    noResults = []

    taskIds = {}

    for lang in allRuns:
        taskIds[lang] = {}
        for llm in allRuns[lang]:
            for bench in allRuns[lang][llm]:
                taskIds[lang][bench] = {}
                runId = allRuns[lang][llm][bench]
                if not (len(runId) == 0):
                    try:
                        print(f"Downloading run ID: {runId}")
                        subargs = ["uv", "run", THIS_DIR / "wandb_pull_detailed_results.py", 
                                "--run", RUN_URL_BASE + runId,
                                "--out", EXPORTS / runId
                                ]
                        if args.overwrite:
                            subargs.append("--overwrite")
                        if args.debug:
                            subargs.insert(0,"echo")
                        subprocess.call(subargs) 
                    except KeyboardInterrupt:
                        raise KeyboardInterrupt
                    except:
                        print(f"Skipping run ID: {runId}")    

                    results = EXPORTS / runId / "detailed_results.table.json"
                    if (results.exists()):
                        analysis = EXPORTS / runId / "analysis.json"
                        if (not analysis.exists()):
                            print(f"Generating analysis for {runId}")
                            try:
                                subargs = ["uv", "run", THIS_DIR / "analyze_wandb_runs.py", "--rundir", EXPORTS / runId]
                                if args.debug:
                                    subargs.insert(0,"echo")
                                subprocess.call(subargs)
                            except Exception as e:
                                raise e
                        else:
                            print(f"Analysis already exists for {runId}.")

                        entryBase = {
                            "Language": lang,
                            "LLM": llm, 
                            "Benchmark": bench, 
                            "WandB ID": runId
                        }
                    
                        analysisJson = None
                        with open(analysis, "r") as f:
                            analysisJson = json.loads(f.read())
                        
                        entries = []
                        for e in analysisJson:
                            entry = entryBase.copy()

                            name = e["name"]

                            taskId = taskIds[lang][bench].get(name, len(taskIds[lang][bench]))
                            taskIds[lang][bench][name] = taskId

                            entry["Task ID"] = idLabel(lang, bench, taskId)
                            entry["Success"] = int(e["success"])
                            entry["Specification length"] = e["inLen"]
                            entry["Solution length"] = e["outLen"]
                            entry["Spec ratio"] = e["ratio"]
                            entries.append(entry)

                        with open(CSV, 'a', newline='') as outcsv:
                            writer = csv.DictWriter(outcsv, fieldnames=FIELDNAMES)
                            for e in entries:
                                pass
                                writer.writerow(e)
                    else:
                        print(f"No results table for {runId}. Cannot proceed.")
                        noResults.append(runId)

    with open(TASKS, "w") as tasks:
        writer = csv.DictWriter(tasks, fieldnames=FIELDNAMES_TASKS)
        writer.writeheader()
        for lang in taskIds:
            for bench in taskIds[lang]:
                for task in taskIds[lang][bench]:
                    writer.writerow(
                        {
                            "Task ID": idLabel(lang, bench, taskIds[lang][bench][task]),
                            "Task": task
                        }
                    )

    print("The following runs were ignored:")
    with open(SKIPPED, "w") as f:
        for x in noResults:
            print(x)
            print(x, file= f)

if __name__ == "__main__":
    main()