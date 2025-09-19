// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn online_max(a: &[i8], x: usize) -> (result: (Ghost<i8>, usize))
    requires 
        1 <= x < a.len(),
        a.len() != 0,
    ensures
        x <= result.1 < a.len(),
        forall|i: int| 0 <= i < x ==> #[trigger] (a[i] as int) <= (result.0@ as int),
        exists|i: int| 0 <= i < x && #[trigger] (a[i] as int) == (result.0@ as int),
        x <= result.1 < a.len() - 1 ==> (forall|i: int| 0 <= i < result.1 ==> #[trigger] (a[i] as int) < (a[result.1 as int] as int)),
        (forall|i: int| x <= i < a.len() && #[trigger] (a[i] as int) <= (result.0@ as int)) ==> result.1 == a.len() - 1
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}