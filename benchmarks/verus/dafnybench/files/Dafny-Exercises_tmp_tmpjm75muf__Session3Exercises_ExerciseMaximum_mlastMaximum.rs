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
    assume(false);
    0
}
// </vc-code>

fn main() {}

}

// Algorithm : from left to right
// Algorithm : from right to left