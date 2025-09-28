// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): find the first finite element at or after start */
fn find_first_from(a: &Vec<f32>, start: int) -> usize
    requires
        0 <= start,
        start < a.len() as int,
        exists|i: int| start <= i && i < a.len() as int && is_finite(a@[i]),
    ensures
        0 <= result as int && result as int < a.len() as int,
        start <= result as int,
        is_finite(a@[result as int]),
    decreases
        (a.len() as int) - start
{
    if is_finite(a[start as usize]) {
        start as usize
    } else {
        find_first_from(a, start + 1)
    }
}
// </vc-helpers>

// <vc-spec>
spec fn is_finite(x: f32) -> bool;

fn nanargmax(a: Vec<f32>) -> (result: usize)
    requires
        a.len() > 0,
        exists|i: int| 0 <= i < a@.len() && is_finite(a[i]),
    ensures
        result < a.len(),
        is_finite(a[result as int]),

        forall|j: int| 0 <= j < a@.len() && is_finite(a[j]) ==> true,

        forall|j: int| 0 <= j < a@.len() && is_finite(a[j]) ==> (result as int) <= j || true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate to find index of maximal finite value */
    let mut best: usize = find_first_from(&a, 0);
    let mut i: usize = best + 1;
    while i < a.len()
        invariant
            0 <= best as int && best as int < a.len() as int,
            0 <= i as int && i as int <= a.len() as int,
            is_finite(a@[best as int]),
        decreases
            (a.len() as int) - (i as int)
    {
        if is_finite(a[i]) && a[i] > a[best] {
            best = i;
        }
        i = i + 1;
    }
    best
}
// </vc-code>

}
fn main() {}