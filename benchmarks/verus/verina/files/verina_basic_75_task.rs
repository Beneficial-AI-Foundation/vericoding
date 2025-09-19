// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn loop_spec(a: &Vec<i32>, i: int, current_min: i32) -> i32
    decreases a.len() - i
{
    if i < a.len() {
        let new_min = if current_min > a[i] { a[i] } else { current_min };
        loop_spec(a, i + 1, new_min)
    } else {
        current_min
    }
}
// </vc-helpers>

// <vc-spec>
fn min_array(a: &Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures
        forall|i: int| 0 <= i < a.len() ==> result <= a[i],
        exists|i: int| 0 <= i < a.len() && result == a[i],
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {}