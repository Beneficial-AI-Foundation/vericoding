use vstd::prelude::*;

verus! {

//Algorithm 1: From left to right return the first

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut max_idx: usize = 0;
    let mut j: usize = 1;
    
    while j < v.len()
        invariant
            0 <= max_idx < j <= v.len(),
            forall|k: int| 0 <= k < j ==> v@[max_idx as int] >= v@[k],
        decreases v.len() - j,
    {
        if v[j] > v[max_idx] {
            max_idx = j;
        }
        j = j + 1;
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