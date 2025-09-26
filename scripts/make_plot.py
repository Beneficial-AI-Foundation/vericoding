#!/usr/bin/env python3

import argparse
from pathlib import Path
import json

from math import ceil

import matplotlib.pyplot as plt
import matplotlib.ticker as mtick
import matplotlib.colors as mcol

from analyze_wandb_runs import ANALYSIS_FILE

PLOT_FILE = "plot.pdf"
N_DIGITS = 2
MAXY_COEF = 1.08

PARAMS = {
    "ratio": 1.0,  # 10**N_DIGITS,
    "inLen": 0,
    "outLen": 0,
}

X_LABELS = {
    "inLen": "Specification (characters)",
    "outLen": "Solution (characters)",
    "ratio": "Spec ratio",
}


def normalizeRatio(r):
    # We normalize the ratios by rounding to N decimals and multiplying by 10^N to get ints
    return int((10**N_DIGITS) * round(r, N_DIGITS))


def floatRatio(r):
    return float(r) / (10**N_DIGITS)


FORMATTING = {
    "ratio": lambda x: f"{x:0.{N_DIGITS}f}",
    "inLen": lambda x: f"{ceil(x)}",
    "outLen": lambda x: f"{ceil(x)}",
}


def getBucketIdx(lst, elem):
    # Find the last element not greater than elem (first in reversed order), get its index
    return lst.index(next(filter(lambda x: x <= elem, reversed(lst)), lst[0]))


def main() -> None:
    p = argparse.ArgumentParser(description="Plots an analysis.json")

    p.add_argument(
        "--rundir",
        required=True,
        help="Run directory root (pull default: wandb_exports/<run_id>). Run analyze_wandb_runs.py to generate an analysis file first.",
    )
    p.add_argument("--out", default=None, help="Output directory (default: rundir)")
    p.set_defaults(_full=True)
    p.add_argument(
        "--short-labels", dest="_full", action="store_false", help="Print short labels"
    )
    p.set_defaults(_show=False)
    p.add_argument("--show", dest="_show", action="store_true", help="Show plot")
    p.add_argument(
        "--buckets", default=10, type=int, help="Number of buckets (default: 10)"
    )

    args = p.parse_args()
    rundir = Path(args.rundir)
    runid = rundir.name
    plot = Path(args.out or rundir.joinpath(PLOT_FILE))
    analysis = rundir.joinpath(ANALYSIS_FILE)

    # minRatioNormalized = 10**N_DIGITS

    try:
        asJson = []
        with open(analysis, "r") as f:
            asJson = json.loads(f.read())

        maxima = PARAMS.copy()

        for entry in asJson:
            # r = normalizeRatio(entry["ratio"])
            # entry.update({"ratio": r})

            for paramName in maxima:
                v = entry[paramName]
                if v > maxima[paramName]:
                    maxima[paramName] = v

        widths = {k: float(maxima[k] - PARAMS[k]) / args.buckets for k in maxima}

        cutoffs = {
            p: [round(PARAMS[p] + x * widths[p], N_DIGITS) for x in range(args.buckets)]
            for p in PARAMS
        }

        results = {
            p: [{"cutoff": c, "elems": [], "successes": 0} for c in cutoffs[p]]
            for p in PARAMS
        }

        nSuccess = 0
        for entry in asJson:
            success = entry["success"]
            name = entry["name"]

            successVal = 1 if success else 0
            nSuccess += successVal

            for p in PARAMS:
                bucketIdx = getBucketIdx(cutoffs[p], entry[p])
                results[p][bucketIdx]["elems"].append(name)
                results[p][bucketIdx]["successes"] += successVal

        globalSuccessRate = float(nSuccess) / float(len(asJson))

        rbounds = {
            p: [FORMATTING[p](c) for c in cutoffs[p][1:]] + ["\u221e"] for p in PARAMS
        }

        shortLabels = {p: [f"{FORMATTING[p](c)}+" for c in cutoffs[p]] for p in PARAMS}

        longLabels = {
            p: [
                f"[{FORMATTING[p](cutoffs[p][i])}, {rbounds[p][i]})"
                for i in range(args.buckets)
            ]
            for p in PARAMS
        }

        labels = longLabels if (args._full) else shortLabels

        successRatios = {
            p: [
                float(x["successes"]) / len(x["elems"]) if len(x["elems"]) > 0 else 0.0
                for x in results[p]
            ]
            for p in PARAMS
        }

        fig, axs = plt.subplots(1, 3, sharey=True)
        fig.suptitle(f"Vericoding success - {runid}")
        axs[0].set(ylabel="Success rate", ylim=(0, 1.1))
        axs[0].yaxis.set_major_formatter(mtick.FuncFormatter(lambda y, _: f"{y:.0%}"))
        for i, p in enumerate(successRatios):
            axs[i].xaxis.grid(True)
            for bucketIdx in range(len(successRatios[p])):
                axs[i].plot(labels[p], successRatios[p])
                axs[i].set(xlabel=X_LABELS[p])
                axs[i].set_facecolor(mcol.ColorConverter.to_rgba("#ADD8E6", 0.3))
                axs[i].tick_params(labelrotation=45)
                axs[i].axhline(
                    globalSuccessRate, linestyle="--", label="Global success rate"
                )

        _handles, _labels = axs[-1].get_legend_handles_labels()

        plt.legend(_handles[-1:], _labels[-1:])
        fig.align_xlabels()
        plt.tight_layout()
        plt.savefig(plot)
        print(f"Saved to {plot}")
        if args._show:
            plt.show()

    except FileNotFoundError:
        print(
            f"{ANALYSIS_FILE} not found at {rundir}. Run analyze_wandb_runs.py first."
        )


if __name__ == "__main__":
    main()
