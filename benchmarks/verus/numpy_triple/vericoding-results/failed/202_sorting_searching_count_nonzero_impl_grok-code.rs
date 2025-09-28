// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn count_zeros_up_to(i: usize, a: Seq<i8>) -> (zeros: nat)
    requires
        i <= a.len(),
    ensures
        zeros <= i as nat,
        zeros == if i == 0 { 0 as nat } else { count_zeros_up_to(i - 1, a) + (if a[(i - 1) as int] == 0 { 1 } else { 0 }) as nat },
    decreases i,
{
    /* helper modified by LLM (iteration 5): Converted to spec fn to allow nat and int types, fixed indexing in body to use spec Seq access. */
    if i == 0 {
        0
    } else {
        count_zeros_up_to(i - 1, a) + if a[(i - 1) as int] == 0 { 1 } else { 0 }
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
    /* code modified by LLM (iteration 5): Used exec vector access instead of ghost seq access with int to fix compilation. */
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count == i as nat - count_zeros_up_to(i, a@),
            count <= i,
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