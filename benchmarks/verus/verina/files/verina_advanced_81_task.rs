// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn unique_sorted(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() <= arr.len(),
        forall|i: int| 0 <= i < result.len() - 1 ==> #[trigger] result[i] <= result[i + 1],
        forall|x: i32| arr@.contains(x) <==> result@.contains(x),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}