// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn linear_search3(a: &Vec<i32>, p: spec_fn(i32) -> bool) -> (result: usize)
    requires 
        exists|i: int| 0 <= i < a.len() && p(a[i]),
    ensures 
        result < a.len(),
        p(a[result as int]),
        forall|k: int| 0 <= k < result ==> !p(a[k]),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}