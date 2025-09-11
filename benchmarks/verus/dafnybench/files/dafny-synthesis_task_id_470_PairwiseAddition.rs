// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn pairwise_addition(a: &[i32]) -> (result: Vec<i32>)
    requires
        a.len() % 2 == 0,
    ensures
        result.len() == a.len() / 2,
        forall|i: int| 0 <= i < result.len() ==> result[i as int] == a[2*i] + a[2*i + 1],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}