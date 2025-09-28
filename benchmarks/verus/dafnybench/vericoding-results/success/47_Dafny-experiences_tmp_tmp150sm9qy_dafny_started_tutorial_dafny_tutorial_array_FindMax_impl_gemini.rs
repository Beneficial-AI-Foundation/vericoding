// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_max(a: &[i32]) -> (i: usize)

    requires 
        a.len() > 0,
    ensures
        i < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[i as int],
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut j: usize = 1;
    while j < a.len()
        invariant
            0 < a.len(),
            j <= a.len(),
            i < j,
            forall|k: int| 0 <= k < j as int ==> a[k] <= a[i as int],
        decreases a.len() - j
    {
        if a[j] > a[i] {
            i = j;
        }
        j = j + 1;
    }
    i
}
// </vc-code>

}
fn main() {}