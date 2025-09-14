// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)

    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1,

    ensures
        odd_index < v.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            exists |q:int| i <= q < v.len() && v[q] % 2 == 1,
        decreases v.len() - i,
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i = i + 1;
    }
    unreached()
}
// </vc-code>

}
fn main() {}