// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_amazing_numbers(n: usize, arr: Vec<usize>) -> (result: Vec<i32>)
    requires
        n > 0,
        arr.len() == n,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i] >= 1 && #[trigger] arr[i] <= n,
    ensures
        result.len() == n,
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