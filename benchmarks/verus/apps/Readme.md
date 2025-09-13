yaml files generated with `code2verus --benchmark ../benchmarks/dafny/apps/yaml/ --source-language dafny --target-language verus --file-pattern "*.yaml" --max-concurrent 10 --save-debug --debug-report --debug-summary` where code2verus is from #181. 

The verus files were generated with `uv run src/convert_from_yaml.py --bench benchmarks/verus/apps --suffix rs`.