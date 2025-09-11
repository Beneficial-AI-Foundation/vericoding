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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}