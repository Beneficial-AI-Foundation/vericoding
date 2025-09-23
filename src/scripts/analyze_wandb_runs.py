#!/usr/bin/env python3

import argparse
from pathlib import Path
import json

RESULTS_FILE = "detailed_results.table.json"
ANALYSIS_FILE = "analysis.json"
OUTPUT_COLUMN = "final_output"
ORIGINAL_COLUMN = "original_spec"
NAME_COLUMN = "file_name"
SUCCESS_COLUMN = "success"

def main() -> None:
    
    p = argparse.ArgumentParser(description="Analyzes runs fetched by wandb_pull_run_files.")
    
    p.add_argument("--rundir", required=True, help="Run directory root (pull default: wandb_exports/<run_id>)")
    p.add_argument("--out", default=None, help="Output directory (default: rundir)")
    p.set_defaults(_display=False)
    p.add_argument("--display", dest="_display", action="store_true", help="Also print to stdout")

    args = p.parse_args()
    rundir = Path(args.rundir)
    analysis = Path(args.out or rundir.joinpath(ANALYSIS_FILE))
    results = rundir.joinpath(RESULTS_FILE)
    display = args._display

    try:

        analysisData = []

        with open(results, "r") as f:
            asJson = json.loads(f.read())
            cols = asJson["columns"]
            
            originalIdx = cols.index(ORIGINAL_COLUMN)
            outIdx = cols.index(OUTPUT_COLUMN)
            nameIdx = cols.index(NAME_COLUMN)
            succIdx = cols.index(SUCCESS_COLUMN)
            
            data = asJson["data"]

            for instance in data:
                name =  Path(instance[nameIdx]).stem
                original = instance[originalIdx]
                output = instance[outIdx]
                success = instance[succIdx]

                len0 = len(original)
                len1 = len(output)

                ratio = -1 if (len0 == 0) else float(len1) / float(len0)

                if (display):
                    print(f"Name: {name}")
                    print(f"Success: {success}")
                    print(f"Input specification length: {len0}")
                    print(f"Solution length: {len1}")
                    print(f"Spec ratio: {ratio}", end="\n\n")

                analysisData.append({
                    "name": name,
                    "success": success,
                    "inLen": len0,
                    "outLen": len1,
                    "ratio": ratio
                })
        
        with open(analysis, "w") as f:
            f.write(json.dumps(analysisData, separators=(',', ':')))
        
        print(f"Analyzed {len(analysisData)} instances. Results saved to\n{analysis.absolute()}")

    except FileNotFoundError:
        print(f"{RESULTS_FILE} not found at {results.parent}.")
        

if __name__ == "__main__":
    main()
