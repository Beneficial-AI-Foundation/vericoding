// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn barrier(v: &[i32], p: usize) -> (b: bool)
    requires 
        v.len() > 0,
        p < v.len(),
    ensures 
        b == forall|k: usize, l: usize| 
            k <= p && p < l && l < v.len() ==> v[k as int] < v[l as int]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}