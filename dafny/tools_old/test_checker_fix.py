#!/usr/bin/env python3

from vericode_checker import verify_specifications

# Test the fix on the problematic file
orig_file = 'benchmarks/test_output_fixed/debug/verified-using-dafny_tmp_tmp7jatpjyn_longestZero_longestZero/verified-using-dafny_tmp_tmp7jatpjyn_longestZero_longestZero_original.dfy'
gen_file = 'benchmarks/test_output_fixed/debug/verified-using-dafny_tmp_tmp7jatpjyn_longestZero_longestZero/verified-using-dafny_tmp_tmp7jatpjyn_longestZero_longestZero_generated.dfy'

with open(orig_file) as f:
    orig_content = f.read()

with open(gen_file) as f:
    gen_content = f.read()

result = verify_specifications(orig_content, gen_content)
print(f'Verification result: {result}')

if result:
    print("✅ Implementation was found and matched!")
else:
    print("❌ Implementation was not found or matched.") 