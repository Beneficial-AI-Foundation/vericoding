// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed return type to int to fix type mismatch in recursive call */
spec fn count_nonzero_in_seq(s: Seq<i8>, start: int, end: int) -> int
    recommends 0 <= start <= end <= s.len()
    decreases end - start
{
    if start >= end {
        0
    } else {
        (if s[start] != 0 { 1 } else { 0 }) + count_nonzero_in_seq(s, start+1, end)
    }
}
// </vc-helpers>

// <vc-spec>
fn count_nonzero(a: Vec<i8>) -> (count: usize)
    ensures
        count <= a.len(),
        a.len() == 0 ==> count == 0,
        (forall|i: int| 0 <= i < a@.len() ==> a[i] == 0) ==> count == 0,
        (forall|i: int| 0 <= i < a@.len() ==> a[i] != 0) ==> count == a.len(),
        (exists|i: int| 0 <= i < a@.len() && a[i] != 0) ==> count > 0,
        (exists|i: int| 0 <= i < a@.len() && a[i] == 0) ==> count < a.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): adjusted invariant to cast helper result to usize */
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count == count_nonzero_in_seq(a@, 0, i as int) as usize
        decreases a.len() - i
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