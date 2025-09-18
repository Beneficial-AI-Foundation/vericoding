// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): increasing sequence implies distinct elements */
proof fn increasing_implies_distinct(indices: Vec<usize>) ensures forall|i: int, j: int| 0 <= i && i < j && j < (indices.len() as int) && indices[i as usize] < indices[j as usize] ==> indices[i as usize] != indices[j as usize] {
    proof {
        // If indices[i] < indices[j] then they are not equal
        assert(forall|i: int, j: int| 0 <= i && i < j && j < (indices.len() as int) && indices[i as usize] < indices[j as usize] ==> indices[i as usize] != indices[j as usize]);
    }
}
// </vc-helpers>

// <vc-spec>
fn nonzero(a: Vec<f32>) -> (indices: Vec<usize>)
    ensures
        forall|i: int| 0 <= i < indices.len() ==> (indices[i] < a.len() && a[indices[i] as int] != 0.0f32),
        forall|j: int| 0 <= j < a.len() ==> (a[j] != 0.0f32 <==> exists|k: int| 0 <= k < indices.len() && indices[k] == j),
        forall|i1: int, i2: int| 0 <= i1 < i2 < indices.len() ==> indices[i1] < indices[i2],
        forall|i: int, j: int| 0 <= i < j < indices.len() ==> indices[i] != indices[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): collect indices of nonzero elements preserving order and maintain invariants */
    let mut indices: Vec<usize> = Vec::new();
    let mut i: int = 0;
    let len_a: int = a.len() as int;
    while i < len_a {
        invariant 0 <= i && i <= len_a;
        invariant forall|k: int| 0 <= k && k < (indices.len() as int) ==> (indices[k as usize] < a.len() && a[indices[k as usize]] != 0.0f32);
        invariant forall|j: int| 0 <= j && j < i ==> (a[j as usize] != 0.0f32 <==> exists|k: int| 0 <= k && k < (indices.len() as int) && indices[k as usize] == j as usize);
        invariant forall|k1: int, k2: int| 0 <= k1 && k1 < k2 && k2 < (indices.len() as int) ==> indices[k1 as usize] < indices[k2 as usize];
        decreases (len_a - i);
        if a[i as usize] != 0.0f32 {
            indices.push(i as usize);
        }
        i += 1;
    }
    indices
}
// </vc-code>

}
fn main() {}