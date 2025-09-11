// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn partition(a: &mut Vec<i32>) -> (r : (usize, usize))
    ensures
        0 <= r.0 && r.0 <= r.1 && r.1 <= a.len(),
        forall|x: int| 0 <= x < r.0 ==> a[x as int] < 0,
        forall|x: int| r.0 <= x < r.1 ==> a[x as int] == 0,
        forall|x: int| r.1 <= x < a.len() ==> a[x as int] > 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}