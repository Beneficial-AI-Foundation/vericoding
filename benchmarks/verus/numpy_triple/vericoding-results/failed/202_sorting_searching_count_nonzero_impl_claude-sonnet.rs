// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): using direct loop without filter helper */
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            count <= i,
            count <= a.len(),
            count == ({let mut c = 0; let mut j = 0; while j < i { if a[j] != 0 { c = c + 1; } j = j + 1; } c})
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