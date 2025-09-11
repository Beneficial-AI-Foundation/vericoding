// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn online_max(a: &[i32], x: usize) -> (result: (Ghost<i32>, usize))
    requires 
        1 <= x < a.len(),
        a.len() != 0,
    ensures
        x <= result.1 < a.len(),
        forall|i: int| 0 <= i < x ==> #[trigger] a[i] <= result.0@,
        exists|i: int| 0 <= i < x && #[trigger] a[i] == result.0@,
        x <= result.1 < a.len() - 1 ==> (forall|i: int| 0 <= i < result.1 ==> #[trigger] a[i] < a[result.1 as int]),
        (forall|i: int| x <= i < a.len() && #[trigger] a[i] <= result.0@) ==> result.1 == a.len() - 1
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}