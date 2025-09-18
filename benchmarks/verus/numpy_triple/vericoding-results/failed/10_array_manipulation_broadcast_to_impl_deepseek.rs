// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed problematic assert syntax and simplified helpers */
proof fn vector_sequence_identity(v: Vec<f32>)
    ensures v@ == v@
{
}

proof fn index_equality_lemma(v_seq: Seq<f32>, j: int)
    requires 0 <= j < v_seq.len()
    ensures v_seq[j] == v_seq[j]
{
}
// </vc-helpers>

// <vc-spec>
fn broadcast_to(v: Vec<f32>, m: usize) -> (result: Vec<Vec<f32>>)
    requires v.len() > 0,
    ensures
        result.len() == m,

        forall|i: int, j: int| 0 <= i < m && 0 <= j < v.len() ==> #[trigger] result[i][j] == v[j],

        forall|i: int| 0 <= i < m ==> #[trigger] result[i]@ == v@,

        forall|j: int, i1: int, i2: int| 0 <= j < v.len() && 0 <= i1 < m && 0 <= i2 < m ==> 
            #[trigger] result[i1][j] == #[trigger] result[i2][j],

        forall|i: int, j: int| 0 <= i < m && 0 <= j < v.len() ==> exists|k: int| 0 <= k < v.len() && #[trigger] result[i][j] == v[k] && k == j,

        forall|i1: int, i2: int| 0 <= i1 < m && 0 <= i2 < m ==> #[trigger] result[i1]@ == #[trigger] result[i2]@
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Simplified implementation with proper cloning and verification */
{
    let mut result = Vec::with_capacity(m);
    let mut i: usize = 0;
    while i < m
        invariant
            result.len() == i,
            forall|idx: int| 0 <= idx < i ==> result[idx]@ == v@,
            forall|idx: int, j: int| 0 <= idx < i && 0 <= j < v.len() ==> #[trigger] result[idx][j] == v[j],
            forall|j: int, idx1: int, idx2: int| 0 <= j < v.len() && 0 <= idx1 < i && 0 <= idx2 < i ==> 
                #[trigger] result[idx1][j] == #[trigger] result[idx2][j],
            forall|idx: int, j: int| 0 <= idx < i && 0 <= j < v.len() ==> exists|k: int| 0 <= k < v.len() && #[trigger] result[idx][j] == v[k] && k == j,
            forall|idx1: int, idx2: int| 0 <= idx1 < i && 0 <= idx2 < i ==> #[trigger] result[idx1]@ == #[trigger] result[idx2]@
    {
        result.push(v.clone());
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}