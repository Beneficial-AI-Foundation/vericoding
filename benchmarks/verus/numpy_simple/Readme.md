

yaml files generated with `code2verus --benchmark ../benchmarks/lean/numpy_simple/yaml/ --source-language lean --target-language verus --file-pattern "*.yaml" --max-concurrent 10 --save-debug --debug-report --debug-summary > out_verus_numpy_simple_17_09_10_12.txt` where code2verus is from #181.


The verus files were generated with `uv run src/convert_from_yaml.py --bench benchmarks/verus/numpy_simple --suffix rs`.

I ran `verus` on all.
