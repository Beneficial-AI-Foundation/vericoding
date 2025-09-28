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
    let mut candidate = v.len() - 1;
    let mut max_val = v[candidate];
    let mut j = v.len() - 1;

    while j > 0
        invariant
            j <= v.len(),
            candidate < v.len(),
            candidate >= j,
            max_val == v@[candidate as int],
            forall|k: int| (j as int) <= k < (v.len() as int) ==> v@[k] <= max_val,
            forall|k: int| (candidate as int) < k < (v.len() as int) ==> v@[k] < max_val,
        decreases j
    {
        let next_index = j - 1;
        if v[next_index] > max_val {
            candidate = next_index;
            max_val = v[next_index];
        }
        j = next_index;
    }

    candidate
}
// </vc-code>

fn main() {}

}

// Algorithm : from left to right
// Algorithm : from right to left