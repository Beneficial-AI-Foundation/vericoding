// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn swap_first_and_last(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        result.len() == a.len(),
        result[0] == a[a.len() - 1],
        result[result.len() - 1] == a[0],
        forall|i: int| 1 <= i < result.len() - 1 ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}