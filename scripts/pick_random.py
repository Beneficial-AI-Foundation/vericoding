import argparse
import os
import yaml
import random
from typing import List

from pathlib import Path

def pickRandomN(n: int, path: Path) -> List[str]:
    return random.sample(os.listdir(path), n)

def llmname(filename: str) -> str:
    return filename.split("_")[-1].split(".")[0]

def main() -> None:
    p = argparse.ArgumentParser(description="Pick vericoding results uniformly at random and prepare templates")
    p.add_argument("--n", default=5, type=int, help="Number of files chosen uniformly at random")
    p.add_argument("--lang", required=True, choices=["dafny", "lean", "verus"], help="Benchmark language")
    p.add_argument("--bench", required=True, choices=[
        "apps", 
        "bignum", 
        "dafnybench",
        "humaneval",
        "verified-cogen",
        "verina"
        ],
        help="Benchmark name")
    p.set_defaults(_successes=True)
    p.add_argument("--failures", dest="_successes", action="store_false",
                   help="Sample failures instead of successes")
    p.add_argument("--out", default=None, help="Output directory (default: benchmarks/validation/<LANG>/<BENCH>/)")

    args = p.parse_args()

    repo = Path(__file__).parent.parent.resolve()

    bench = repo / "benchmarks"

    out = Path(args.out or (bench / "validation" / args.lang / args.bench))

    out.mkdir(parents=True, exist_ok=True)

    template = bench / "validation" / "analysis_template.yaml"

    sOrF = "success" if args._successes else "failed"

    sources = bench / args.lang / args.bench / "vericoding-results" / sOrF

    randomFiles = pickRandomN(args.n, sources)


    templateFile = None
    with open(template, "r") as stream:
        try:
            templateFile =yaml.safe_load(stream)
        except yaml.YAMLError as exc:
            print(exc)
            exit()

    fpath = out / f"analysis.yaml"
    fyaml = templateFile.copy()
    fyaml["benchmark"] = args.bench
    fyaml["language"] = args.lang
    fyaml["checking-successes"] = sOrF == "success"
    fyaml["files-sampled"] = []


    for f in randomFiles:
        fyaml["files-sampled"].append(
            {
                "file": f,
                "llm": llmname(f),
                "issues-with-spec": "...",
                "issues-with-implementation": "..."
            }
        )
    
    with open(fpath, "w") as outFile:
        yaml.dump(fyaml, outFile, sort_keys=False)

if __name__ == "__main__":
    main()
