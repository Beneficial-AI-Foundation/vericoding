use vstd::prelude::*;

verus! {

//Algorithm 1: From left to right return the first

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
    let mut max_idx = 0;
    let mut i = 1;
    
    while i < v.len()
        invariant
            0 <= max_idx < v.len(),
            1 <= i <= v.len(),
            forall|k: int| 0 <= k < i ==> v[max_idx as int] >= v[k],
        decreases v.len() - i,
    {
        if v[i] > v[max_idx] {
            max_idx = i;
        }
        i += 1;
    }
    
    max_idx
}
// </vc-code>

//Algorithm 2: From right to left return the last




//Algorithm : from left to right
//Algorithm : from right to left

fn main() {
}

}