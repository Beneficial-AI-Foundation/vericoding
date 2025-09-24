python src/convert_from_yaml.py --benchmarks benchmarks
python src/convert_from_yaml.py --all-poor benchmarks
# insert script for computing quality analysis metadata

python src/convert_from_yaml.py --language-tasks benchmarks
python src/formatting/convert_jsonl_to_csv.py benchmarks/dafny_tasks.jsonl
python src/formatting/convert_jsonl_to_csv.py benchmarks/lean_tasks.jsonl
python src/formatting/convert_jsonl_to_csv.py benchmarks/verus_tasks.jsonl
python src/formatting/convert_jsonl_to_csv.py benchmarks/dafny_issues.jsonl
python src/formatting/convert_jsonl_to_csv.py benchmarks/lean_issues.jsonl
python src/formatting/convert_jsonl_to_csv.py benchmarks/verus_issues.jsonl