// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type casting issues and nat/usize conversion */
fn diff_at_index(ary: &Vec<i8>, i: nat) -> (diff: i8)
    requires i < ary.len() - 1,
    ensures diff as int == (ary.index(i + 1) as int) - (ary.index(i) as int),
{
    let idx: usize = i as usize;
    let diff_val = ary[idx + 1] - ary[idx];
    diff_val
}
// </vc-helpers>

// <vc-spec>
fn numpy_ediff1d(ary: Vec<i8>) -> (result: Vec<i8>)
    requires ary.len() > 0,
    ensures 
        result.len() == ary.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == ary[i + 1] as int - ary[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed nat indexing and loop counter increment */
    let mut result = Vec::new();
    let n = ary.len();
    let mut i: usize = 0;
    
    while i < n - 1
        invariant
            i <= n - 1,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == (ary[j + 1] as int) - (ary[j] as int),
        decreases (n - 1) - i,
    {
        let diff = diff_at_index(&ary, i as nat);
        result.push(diff);
        proof {
            assert(i < n - 1);
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}