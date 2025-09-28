use vstd::prelude::*;

verus! {

//Algorithm 1: From left to right return the first

//Algorithm 2: From right to left return the last

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mfirstMaximum(v: &Vec<i32>) -> (i: usize)
    requires v.len() > 0,
    ensures 
        0 <= i < v.len() &&
        (forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k]) &&
        (forall|l: int| 0 <= l < i ==> v[i as int] > v[l]),
    //Algorithm: from left to right
// </vc-spec>
// <vc-code>
{
    let mut max_idx: usize = 0;
    let mut max_val: i32 = v[0];
    let mut i: usize = 1;
    
    while i < v.len()
        invariant 
            0 <= max_idx < i <= v.len(),
            max_val == v@[max_idx as int],
            forall|k: int| 0 <= k < i ==> v@[max_idx as int] >= v@[k],
            forall|l: int| 0 <= l < max_idx ==> v@[max_idx as int] > v@[l],
        decreases v.len() - i,
    {
        if v[i] > max_val {
            max_idx = i;
            max_val = v[i];
        }
        i = i + 1;
    }
    
    max_idx
}
// </vc-code>

//Algorithm : from left to right
//Algorithm : from right to left

fn main() {}

}