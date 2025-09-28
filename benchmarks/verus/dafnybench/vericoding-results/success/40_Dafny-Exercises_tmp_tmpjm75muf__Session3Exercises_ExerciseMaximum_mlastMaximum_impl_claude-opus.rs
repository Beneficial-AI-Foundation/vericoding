use vstd::prelude::*;

verus! {

// Algorithm 1: From left to right return the first
// Algorithm 2: From right to left return the last

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
fn mlast_maximum(v: &[i32]) -> (i: usize)
    requires v.len() > 0
    ensures 
        i < v.len(),
        forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k],
        forall|l: int| i < l < v.len() ==> v[i as int] > v[l],
// </vc-spec>
// <vc-code>
{
    let mut max_idx: usize = 0;
    let mut j: usize = 1;
    
    while j < v.len()
        invariant
            0 <= max_idx < j <= v.len(),
            forall|k: int| 0 <= k < j ==> v@[max_idx as int] >= v@[k],
            forall|l: int| max_idx < l < j ==> v@[max_idx as int] > v@[l],
        decreases v.len() - j,
    {
        if v[j] >= v[max_idx] {
            max_idx = j;
        }
        j = j + 1;
    }
    
    max_idx
}
// </vc-code>

fn main() {}

}

// Algorithm : from left to right
// Algorithm : from right to left