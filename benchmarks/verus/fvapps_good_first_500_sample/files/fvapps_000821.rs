// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_pattern(k: usize) -> (result: Vec<String>)
    requires k >= 2 && k <= 100,
    ensures 
        result.len() == k,
        forall|i: int| 0 <= i < k ==> result[i]@.len() > 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}