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
    let mut max_index = 0;
    let mut i = 1;
    
    while i < v.len()
        invariant
            0 <= max_index < v.len(),
            1 <= i <= v.len(),
            forall|k: int| 0 <= k < i ==> v[max_index as int] >= v[k],
            forall|l: int| 0 <= l < max_index ==> v[max_index as int] > v[l],
        decreases v.len() - i,
    {
        if v[i] > v[max_index] {
            max_index = i;
        }
        i += 1;
    }
    
    assert(forall|k: int| 0 <= k < v.len() ==> v[max_index as int] >= v[k]);
    assert(forall|l: int| 0 <= l < max_index ==> v[max_index as int] > v[l]);
    
    max_index
}
// </vc-code>

//Algorithm : from left to right
//Algorithm : from right to left

fn main() {}

}