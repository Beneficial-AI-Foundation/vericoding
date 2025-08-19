from vericode_parser import extract_impl_blocks

with open('test_output_fixed/debug/dafny-synthesis_task_id_70_AllSequencesEqualLength/dafny-synthesis_task_id_70_AllSequencesEqualLength_generated.dfy') as f:
    content = f.read()

blocks = extract_impl_blocks(content)
if blocks:
    print('First 10 lines of first IMPL block:')
    for i, line in enumerate(blocks[0].splitlines()[:10]):
        print(f'{i+1}: {repr(line)}')
else:
    print('No IMPL blocks found') 