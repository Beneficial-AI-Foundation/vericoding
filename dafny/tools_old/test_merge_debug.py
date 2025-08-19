#!/usr/bin/env python3

from vericode_checker import restore_specifications
from vericode_parser import extract_impl_blocks, get_signature, extract_body

# Test the merging issue
orig_file = 'benchmarks/test_output_fixed/debug/SENG2011_tmp_tmpgk5jq85q_ass2_ex1_check/SENG2011_tmp_tmpgk5jq85q_ass2_ex1_check_original.dfy'
gen_file = 'benchmarks/test_output_fixed/debug/SENG2011_tmp_tmpgk5jq85q_ass2_ex1_check/SENG2011_tmp_tmpgk5jq85q_ass2_ex1_check_generated.dfy'

with open(orig_file) as f:
    orig_content = f.read()

with open(gen_file) as f:
    gen_content = f.read()

print("=== DEBUGGING MERGE ISSUE ===")
print()

# Check IMPL blocks extraction
impl_blocks = extract_impl_blocks(gen_content)
print(f"Found {len(impl_blocks)} IMPL blocks in generated code")
for i, block in enumerate(impl_blocks):
    sig = get_signature(block)
    body = extract_body(block)
    print(f"Block {i}:")
    print(f"  Signature: {repr(sig)}")
    print(f"  Body length: {len(body)} chars")
    print(f"  Body preview: {repr(body[:100])}...")
    print()

# Test the restore_specifications function
merged_content = restore_specifications(orig_content, gen_content)
print("=== MERGED CONTENT ===")
print(merged_content)
print()

# Check if the check() method has a body in the merged content
if "method check()" in merged_content:
    check_start = merged_content.find("method check()")
    check_end = merged_content.find("}", check_start)
    if check_end != -1:
        check_method = merged_content[check_start:check_end+1]
        print("=== CHECK METHOD IN MERGED CONTENT ===")
        print(check_method)
        print()
        
        if "{}" in check_method:
            print("❌ Method body is empty!")
        else:
            print("✅ Method has implementation!")
    else:
        print("❌ Could not find end of check method")
else:
    print("❌ Could not find check method in merged content") 