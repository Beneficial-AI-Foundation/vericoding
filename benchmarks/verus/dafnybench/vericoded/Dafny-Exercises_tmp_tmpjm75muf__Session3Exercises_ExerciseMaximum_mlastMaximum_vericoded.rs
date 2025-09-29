use vstd::prelude::*;

verus! {

// Algorithm 1: From left to right return the first
// Algorithm 2: From right to left return the last

// <vc-helpers>

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
    let mut max_idx = 0;
    let mut i = 1;
    
    while i < v.len()
        invariant
            0 <= max_idx < v.len(),
            1 <= i <= v.len(),
            forall|k: int| 0 <= k < i ==> v[max_idx as int] >= v[k],
            forall|l: int| max_idx < l < i ==> v[max_idx as int] > v[l],
        decreases v.len() - i
    {
        if v[i] >= v[max_idx] {
            max_idx = i;
        }
        i += 1;
    }
    
    max_idx
}
// </vc-code>

fn main() {}

}

// Algorithm : from left to right
// Algorithm : from right to left