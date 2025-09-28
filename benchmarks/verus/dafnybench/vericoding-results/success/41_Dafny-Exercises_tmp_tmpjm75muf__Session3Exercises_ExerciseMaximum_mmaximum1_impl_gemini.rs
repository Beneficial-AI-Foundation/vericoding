// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mmaximum1(v: &[i32]) -> (i: usize)
    requires v.len() > 0,
    ensures 
        0 <= i < v.len(),
        forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k],
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut j: usize = 1;
    while j < v.len()
        invariant
            0 <= i < v.len(),
            1 <= j <= v.len(),
            forall|k: int| 0 <= k < j ==> v[i as int] >= v[k],
        decreases v.len() - j
    {
        if v[j] > v[i] {
            i = j;
        }
        j = j + 1;
    }
    i
}
// </vc-code>

}
fn main() {}