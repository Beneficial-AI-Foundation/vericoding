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
    let mut max_index: usize = 0;
    for i in 1..v.len()
        invariant
            0 <= max_index < i,
            forall |k: int| 0 <= k < i ==> v@[max_index as int] >= v@[k],
    {
        if v[i] > v[max_index] {
            max_index = i;
        }
    }
    max_index
}
// </vc-code>

//Algorithm 2: From right to left return the last




//Algorithm : from left to right
//Algorithm : from right to left

fn main() {
}

}