rm -rf benchmarks/lean/numpy_all
rm -rf benchmarks/lean/numpy_yaml
rm -rf benchmarks/lean/numpy_bad
rm -rf benchmarks/lean/numpy_fix
rm benchmarks/lean/parsing_results.json
rm benchmarks/lean/wrong_format.txt

python3 src/formatting/numpy_triple_copy_files.py
python3 src/formatting/numpy_triple_replace_files.py
python3 src/formatting/numpy_triple_check_format.py
python3 src/formatting/numpy_triple_parse_files.py
python3 src/formatting/numpy_triple_impl_proof.py 
python3 src/formatting/numpy_triple_empty_descriptions.py