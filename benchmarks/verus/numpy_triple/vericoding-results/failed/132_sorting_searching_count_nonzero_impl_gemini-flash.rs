// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add `decreases` clause for recursive spec function. */
spec fn count_idx(start: usize, end: usize, a: Seq<i32>) -> nat
decreases (end - start)
{
    if start >= end {
        0
    } else if a.index(start as int) != 0 {
        (1 + count_idx(start.checked_add(1).unwrap(), end, a)) as nat
    } else {
        count_idx(start.checked_add(1).unwrap(), end, a)
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
/* code modified by LLM (iteration 5): No changes needed in vc-code, error was in helper function. */
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            count <= i,
            count == count_idx(0, i, a@)
    {
        if a[i] != 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>

}
fn main() {}