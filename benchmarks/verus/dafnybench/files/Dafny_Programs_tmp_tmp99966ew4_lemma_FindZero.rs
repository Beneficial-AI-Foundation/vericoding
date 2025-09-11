// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_zero(a: &[i32]) -> (index: i32)
    requires
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 0,
        forall|i: int| 0 < i < a.len() ==> #[trigger] a[i-1] - 1 <= a[i],
    ensures
        (index < 0 ==> forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] != 0),
        (0 <= index ==> index < a.len() && a[index as int] == 0),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}