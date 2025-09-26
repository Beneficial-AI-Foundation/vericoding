#!/usr/bin/env python3

import argparse
from pathlib import Path
import csv


import matplotlib.pyplot as plt
import matplotlib.ticker as mtick
import matplotlib.colors as mcol

from pull_all import CSV_FILENAME, DEFAULT_EXPORTS as DEFAULT_CSV_DIR

N_DIGITS = 2

PARAMS = {"Spec ratio": 0.0, "Specification length": 0, "Solution length": 0}

PARAM_TYPES = {"Spec ratio": float, "Specification length": int, "Solution length": int}

X_LABELS = {
    "Spec ratio": "Spec ratio percentile",
    "Specification length": "Specification length percentile",
    "Solution length": "Solution length percentile",
}

SUFFIXES = {
    "Spec ratio": "ratio",
    "Specification length": "inLen",
    "Solution length": "outLen",
}


def plotFile(lang: str, p: str) -> str:
    return f"plot_{lang}_{SUFFIXES[p]}.pdf"


def getBucketIdx(lst, elem, typecast):
    # Find the last element not greater than elem (first in reversed order), get its index
    return lst.index(next(filter(lambda x: x <= typecast(elem), reversed(lst)), lst[0]))


def main() -> None:
    p = argparse.ArgumentParser(description="Plots an analysis.json")

    p.add_argument(
        "--dir",
        default=None,
        help="Path to directory containing CSV (pull default: wandb_exports). Run pull_all.py to generate it first.",
    )
    p.add_argument("--out", default=None, help="Output directory (default: dir)")
    # p.set_defaults(_full=True)
    # p.add_argument("--short-labels", dest="_full", action="store_false", help="Print short labels")
    p.set_defaults(_show=False)
    p.add_argument("--show", dest="_show", action="store_true", help="Show plot")
    p.add_argument(
        "--buckets", default=10, type=int, help="Number of buckets (default: 10)"
    )

    args = p.parse_args()

    csvDir = Path(args.dir or DEFAULT_CSV_DIR)
    csvFile = csvDir / CSV_FILENAME

    errors = []

    try:
        rowsByLangBench = {}
        with open(csvFile, "r") as f:
            reader = csv.DictReader(f)
            for row in reader:
                lang = row["Language"]
                bench = row["Benchmark"]
                if float(row["Spec ratio"]) <= 0.0:
                    errors.append(row)

                else:
                    langDict = rowsByLangBench.get(lang, {})
                    entries = langDict.get(bench, [])
                    entries.append(row)
                    langDict[bench] = entries
                    rowsByLangBench[lang] = langDict

        cutoffs = {
            lang: {
                b: {
                    p: [
                        PARAM_TYPES[p](
                            sorted(
                                rowsByLangBench[lang][b],
                                key=lambda row: PARAM_TYPES[p](row[p]),
                            )[x * (len(rowsByLangBench[lang][b]) // args.buckets)][p]
                        )
                        for x in range(args.buckets)
                    ]
                    for p in PARAMS
                }
                for b in rowsByLangBench[lang]
            }
            for lang in rowsByLangBench
        }

        results = {
            lang: {
                b: {
                    p: [
                        {"cutoff": c, "elems": set(), "successes": set()}
                        for c in cutoffs[lang][b][p]
                    ]
                    for p in PARAMS
                }
                for b in rowsByLangBench[lang]
            }
            for lang in rowsByLangBench
        }

        for lang in rowsByLangBench:
            for bench in rowsByLangBench[lang]:
                for row in rowsByLangBench[lang][bench]:
                    success = int(row["Success"])
                    taskId = row["Task ID"]
                    for p in PARAMS:
                        bucketIdx = getBucketIdx(
                            cutoffs[lang][bench][p], row[p], PARAM_TYPES[p]
                        )
                        results[lang][bench][p][bucketIdx]["elems"].add(taskId)
                        if success == 1:
                            results[lang][bench][p][bucketIdx]["successes"].add(taskId)

        labels = {
            p: [
                f"\u2265{round(100.0 // args.buckets) * i}%"
                for i in range(args.buckets)
            ]
            for p in PARAMS
        }

        successRatios = {
            lang: {
                b: {
                    p: [
                        float(len(x["successes"])) / len(x["elems"])
                        if len(x["elems"]) > 0
                        else 0.0
                        for x in results[lang][b][p]
                    ]
                    for p in PARAMS
                }
                for b in results[lang]
            }
            for lang in results
        }

        for lang in rowsByLangBench:
            for p in PARAMS:
                plot = Path(args.out or csvDir) / plotFile(lang, p)

                fig, ax = plt.subplots()
                fig.suptitle(f"Vericoding success - {lang.capitalize()}")
                ax.set(ylabel="Success rate", ylim=(-0.1, 1.1))
                ax.yaxis.set_major_formatter(
                    mtick.FuncFormatter(lambda y, _: f"{y:.0%}")
                )

                ax.set(xlabel=X_LABELS[p])
                ax.set_facecolor(mcol.ColorConverter.to_rgba("#ADD8E6", 0.3))
                ax.tick_params(labelrotation=45)
                ax.xaxis.grid(True)

                for bench in sorted(rowsByLangBench[lang]):
                    ratios = successRatios[lang][bench][p]
                    ax.plot(labels[p], ratios, label=bench)

                fig.align_xlabels()
                plt.tight_layout()
                plt.legend()
                plt.savefig(plot)
                print(f"Saved to {plot}")
                if args._show:
                    plt.show()

    except FileNotFoundError:
        print(f"{CSV_FILENAME} not found at {csvDir}. Run pull_all.py first.")


if __name__ == "__main__":
    main()
