// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove erroneous `Seq::fill` calls and replace with direct sequence comparison to fix compilation */
proof fn lemma_nth_equals_v_nth(v: Seq<f32>, m: usize, idx: int)
    requires
        v.len() > 0
    ensures
        v == v
{
    /* No assertion needed for `v == v` */
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
/* code modified by LLM (iteration 5): remove `capacity()` assertion that caused compilation failure */
{
    let mut result: Vec<Vec<f32>> = Vec::new();
    result.reserve(m);

    let ghost ghost_v_len = v.len() as nat;

    let mut i: usize = 0;
    while i < m
        invariant
            0 <= i <= m,
            result.len() == i,
            result.capacity() == m,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k]@ == v@,
            forall|k_idx: int| 0 <= k_idx < i ==> (forall|j: int| 0 <= j < v.len() ==> #[trigger] result[k_idx][j] == v[j]),
            forall|k1: int, k2: int| 0 <= k1 < i && 0 <= k2 < i ==> #[trigger] result[k1]@ == #[trigger] result[k2]@
    {
        let mut current_vec: Vec<f32> = Vec::new();
        current_vec.reserve(v.len());
        let mut j: usize = 0;
        while j < v.len()
            invariant
                0 <= j <= v.len(),
                j as nat <= v.len(),
                current_vec.len() == j,
                current_vec.capacity() == v.len(),
                forall|k: int| 0 <= k < j ==> current_vec[k] == v[k]
        {
            current_vec.push(v[j]);
            j = j + 1;
        }
        result.push(current_vec);
        i = i + 1;
    }
    
    assert(result.len() == m);
    assert forall|idx: int| 0 <= idx < m implies result[idx]@ == v@ by {
        assert(v@ == v@) by {
            lemma_nth_equals_v_nth(v@, m, 0);
        };
        assert(result[idx]@ == v@);
    }

    result
}
// </vc-code>

}
fn main() {}