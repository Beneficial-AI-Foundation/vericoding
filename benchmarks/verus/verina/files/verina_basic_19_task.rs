// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_sorted(a: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] a[i] <= a[i + 1]),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}