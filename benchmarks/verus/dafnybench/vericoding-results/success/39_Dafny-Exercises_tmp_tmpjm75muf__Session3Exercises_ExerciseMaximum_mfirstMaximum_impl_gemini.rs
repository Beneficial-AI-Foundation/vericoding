// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mfirstMaximum(v: &Vec<i32>) -> (i: usize)
    requires v.len() > 0,
    ensures 
        0 <= i < v.len() &&
        (forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k]) &&
        (forall|l: int| 0 <= l < i ==> v[i as int] > v[l]),
// </vc-spec>
// <vc-code>
{
    let mut max_idx: usize = 0;
    let mut j: usize = 1;
    while j < v.len()
        invariant
            v.len() > 0,
            0 < j <= v.len(),
            0 <= max_idx < j,
            forall|k: int| 0 <= k < j ==> v@[max_idx as int] >= v@[k],
            forall|l: int| 0 <= l < max_idx ==> v@[max_idx as int] > v@[l],
        decreases v.len() - j
    {
        if v[j] > v[max_idx] {
            max_idx = j;
        }
        j = j + 1;
    }
    max_idx
}
// </vc-code>

}
fn main() {}