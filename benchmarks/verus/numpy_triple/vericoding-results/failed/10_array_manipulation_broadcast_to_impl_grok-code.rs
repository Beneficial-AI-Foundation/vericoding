// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): added proof block to assert sequence equality after clone in loop */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k]@ == v@
        decreases m - i
    {
        result.push(v.clone());
        proof {
            assert(result@[i]@ == v@);
        }
        i += 1;
    }
    proof {
        assert(result.len() == m);
    }
    result
}
// </vc-code>

}
fn main() {}