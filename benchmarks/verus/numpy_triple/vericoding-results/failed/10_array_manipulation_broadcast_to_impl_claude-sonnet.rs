// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma to establish postcondition properties */
proof fn broadcast_postcondition_lemma(result: Vec<Vec<f32>>, v: Vec<f32>, m: usize)
    requires
        result.len() == m,
        forall|i: int| 0 <= i < m ==> #[trigger] result[i]@ == v@,
        forall|i: int| 0 <= i < m ==> result[i].len() == v.len(),
        v.len() > 0
    ensures
        forall|i: int, j: int| 0 <= i < m && 0 <= j < v.len() ==> #[trigger] result[i][j] == v[j],
        forall|i: int, j: int| 0 <= i < m && 0 <= j < v.len() ==> exists|k: int| 0 <= k < v.len() && #[trigger] result[i][j] == v[k] && k == j
{
    assert(forall|i: int, j: int| 0 <= i < m && 0 <= j < v.len() ==> {
        let seq_eq = result[i]@ == v@;
        let idx_eq = result[i][j] == v[j];
        idx_eq
    });
    
    assert(forall|i: int, j: int| 0 <= i < m && 0 <= j < v.len() ==> {
        let k = j;
        0 <= k < v.len() && result[i][j] == v[k] && k == j
    });
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
{
    /* code modified by LLM (iteration 5): added helper lemma call to establish postconditions */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i = 0;
    while i < m
        invariant
            result.len() == i,
            forall|idx: int| 0 <= idx < i ==> #[trigger] result[idx]@ == v@,
            forall|idx: int| 0 <= idx < i ==> result[idx].len() == v.len(),
            forall|idx: int, j: int| 0 <= idx < i && 0 <= j < v.len() ==> #[trigger] result[idx][j] == v[j],
            i <= m
        decreases m - i
    {
        let copy = v.clone();
        result.push(copy);
        proof {
            assert(result[i as int]@ == v@);
            assert(result[i as int].len() == v.len());
            assert(forall|j: int| 0 <= j < v.len() ==> result[i as int][j] == v[j]) by {
                assert(result[i as int]@ == v@);
            };
        }
        i += 1;
    }
    
    proof {
        broadcast_postcondition_lemma(result, v, m);
    }
    
    result
}
// </vc-code>

}
fn main() {}