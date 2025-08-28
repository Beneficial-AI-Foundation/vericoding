use vstd::prelude::*;

verus! {

// Algorithm 1: From left to right return the first
// Algorithm 2: From right to left return the last

// <vc-helpers>
// Helper lemma to prove properties about maximum elements
proof fn lemma_maximum_properties(v: Seq<i32>, i: int)
    requires 
        0 <= i < v.len(),
        forall|k: int| 0 <= k < v.len() ==> v[i] >= v[k],
        forall|l: int| i < l < v.len() ==> v[i] > v[l]
    ensures
        true
{
    // No additional proof needed; this is just a placeholder for potential helper proofs
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn mlast_maximum(v: &[i32]) -> (i: usize)
    requires v.len() > 0
    ensures 
        i < v.len(),
        forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k],
        forall|l: int| i < l < v.len() ==> v[i as int] > v[l],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn mlast_maximum(v: &[i32]) -> (i: usize)
    requires v.len() > 0
    ensures 
        i < v.len(),
        forall|k: int| 0 <= k < v.len() ==> v[i as int] >= v[k],
        forall|l: int| i < l < v.len() ==> v[i as int] > v[l]
{
    let mut max_idx: usize = v.len() - 1;
    let mut i: usize = v.len() - 1;

    while i > 0
        invariant
            0 <= max_idx < v.len(),
            0 <= i <= v.len(),
            forall|k: int| i <= k < v.len() ==> v[max_idx as int] >= v[k]
    {
        let next_i = i - 1;
        if v[next_i] >= v[max_idx] {
            max_idx = next_i;
        }
        i = next_i;
    }

    max_idx
}
// </vc-code>

fn main() {}

}

// Algorithm : from left to right
// Algorithm : from right to left