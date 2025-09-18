// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed type annotations for literals */
spec fn count_nonzero_prefix(a: Vec<i32>, end: int) -> nat
    requires 0 <= end <= a.len()
{
    if end == 0 {
        0nat
    } else {
        (if a@[end-1] != 0 { 1nat } else { 0nat }) + count_nonzero_prefix(a, end-1)
    }
}
// </vc-helpers>

// <vc-spec>
fn count_nonzero(a: Vec<i32>) -> (count: usize)
    ensures
        count <= a.len(),
        a.len() == 0 ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] == 0) ==> count == 0,
        (forall|i: int| 0 <= i < a.len() ==> a[i] != 0) ==> count == a.len(),
        (exists|i: int| 0 <= i < a.len() && a[i] != 0) ==> count > 0,
        (exists|i: int| 0 <= i < a.len() && a[i] == 0) ==> count < a.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed type mismatch by casting usize to int */
{
    let mut count = 0;
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count == count_nonzero_prefix(a, i as int)
    {
        if a[i] != 0 {
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-code>

}
fn main() {}