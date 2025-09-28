// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec prefix_nonzero_count returns usize; use usize literals */
spec fn prefix_nonzero_count(s: Seq<i8>, n: usize) -> usize
    requires
        n <= s.len(),
{
    if n == 0 {
        0usize
    } else {
        prefix_nonzero_count(s, n - 1) + (if s[n - 1] != 0 { 1usize } else { 0usize })
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
{
    /* code modified by LLM (iteration 5): iterative count using usize indices and helper */
    let mut i: usize = 0;
    let mut count: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            count == prefix_nonzero_count(a@, i),
        decreases a.len() - i
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