// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rotate(a: &Vec<i32>, offset: int) -> (result: Vec<i32>)
    requires offset >= 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let src_idx = (i + offset) % (a.len() as int);
            #[trigger] result[i] == a[src_idx]
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed type casting of 'offset' from 'int' to 'usize' by converting 'int' to 'nat', then 'nat' to 'usize', and adjusted indexing to use 'usize' for executable code while preserving 'int' for verification logic */
{
    let mut result: Vec<i32> = Vec::new();
    let len = a.len();
    if len == 0 {
        return result;
    }

    let offset_nat: nat = offset as nat;
    let offset_concrete: usize = offset_nat as usize;

    let mut i: usize = 0;
    while i < len
        invariant
            result.len() == i,
            len == a.len(),
            offset >= 0,
            forall|j: int| 0 <= j < i ==> {
                let src_idx = (j + offset) % (a.len() as int);
                result[j as usize] == a[src_idx as usize]
            },
        decreases len - i
    {
        let src_idx_concrete = (i + offset_concrete) % len;
        result.push(a[src_idx_concrete]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}