#!/usr/bin/env python3

import argparse
from pathlib import Path
import json

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import MaxNLocator

from analyze_wandb_runs import ANALYSIS_FILE

PLOT_FILE = "plot.pdf"
N_DIGITS = 2
MAXY_COEF = 1.08


def normalizeRatio(r):
    # We normalize the ratios by rounding to N decimals and multiplying by 10^N to get ints
    return int( (10**N_DIGITS) * round(r, N_DIGITS) ) 

def floatRatio(r):
    return float(r) / (10**N_DIGITS)

def getBucketIdx(lst, elem):
    # Find the last element not greater than elem (first in reversed order), get its index
    return lst.index(next(filter(lambda x: x <= elem, reversed(lst)), lst[0]))

def main() -> None:
    
    p = argparse.ArgumentParser(description="Plots an analysis.json")
    
    p.add_argument("--rundir", required=True, help="Run directory root (pull default: wandb_exports/<run_id>). Run analyze_wandb_runs.py to generate an analysis file first.")
    p.add_argument("--out", default=None, help="Output directory (default: rundir)")
    p.set_defaults(_full=True)
    p.add_argument("--short-labels", dest="_full", action="store_false", help="Print short labels")
    p.add_argument("--buckets", default=10, type=int, help="Number of buckets (default: 10)")

    args = p.parse_args()
    rundir = Path(args.rundir)
    plot = Path(args.out or rundir.joinpath(PLOT_FILE))
    analysis = rundir.joinpath(ANALYSIS_FILE)

    minRatioNormalized = 10**N_DIGITS

    try:
        asJson = []
        with open(analysis, "r") as f:
            asJson = json.loads(f.read())

        maxRatio = minRatioNormalized

        for entry in asJson:
            r = normalizeRatio(entry["ratio"])
            entry.update({"ratio": r})
            if(r > maxRatio):
                maxRatio = r

        width = (maxRatio - minRatioNormalized) // args.buckets
        bucketCutoffs = [minRatioNormalized + x * width for x in range(args.buckets)]

        results = [
            {
                "cutoff": c,
                "elems": [],
                "successes": 0,
            }
            for c in bucketCutoffs
        ]

        for entry in asJson:
            r = entry["ratio"]
            success = entry["success"]
            name = entry["name"]
            
            bucketIdx = getBucketIdx(bucketCutoffs, r)
            oldResults = results[bucketIdx]

            oldResults["elems"].append(name)
            oldResults["successes"] += 1 if success else 0

        rbounds = [ f"{floatRatio(c):0.2f}" for c in bucketCutoffs[1:]] + ["\u221e"]

        shortLabels = [
            f"{floatRatio(bucketCutoffs[i]):0.2f}+" for i in range(args.buckets)
        ]

        longLabels = [
            f"[{floatRatio(bucketCutoffs[i]):0.2f}, {rbounds[i]})" for i in range(args.buckets)
        ]

        labels = longLabels if (args._full) else shortLabels

        successCounts = {
            'Success': np.array([x["successes"] for x in results]),
            'Failure': np.array([len(x["elems"]) - x["successes"] for x in results]),
        }

        width = 0.6
        bottom = np.zeros(len(labels))

        fig, ax = plt.subplots()
        for state, count in successCounts.items():
            p = ax.bar(labels, count, width, label=state, bottom=bottom)
            bottom += count

            ax.bar_label(p, label_type='edge')

        ax.set_title('Successes by spec ratio')
        ax.legend()
        ax.yaxis.set_major_locator(MaxNLocator(integer=True))

        maxy = max([successCounts["Success"][i] + successCounts["Failure"][i] for i in range(len(results))])

        ax.set(xlabel='Spec ratio', ylim=(0, maxy * MAXY_COEF))
        plt.xticks(rotation=45)
        plt.tight_layout()
        plt.savefig(plot)

        # heights = [
        #     float(x["successes"]) / len(x["elems"]) if len(x["elems"]) > 0 else 0.0 for x in results
        # ]

        # fig, ax = plt.subplots()
        # bar_container = ax.bar(labels, heights)
        # ax.set(ylabel='Success ratio', title='Success ratio by spec ratio', ylim=(0, 1.1))
        # ax.set(xlabel='Spec ratio') #, xlim=(1,floatRatio(maxRatio))
        # ax.bar_label(bar_container)
        # plt.xticks(rotation=60)
        # plt.tight_layout()

    except FileNotFoundError:
        print(f"{ANALYSIS_FILE} not found at {rundir}. Run analyze_wandb_runs.py first.")
        

if __name__ == "__main__":
    main()
