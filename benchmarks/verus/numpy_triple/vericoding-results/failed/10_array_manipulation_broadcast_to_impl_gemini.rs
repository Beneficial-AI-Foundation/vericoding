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
    /* code modified by LLM (iteration 5): used assert by(ext_equal) to prove sequence equality */
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            i <= m,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result[k]@ == v@,
        decreases m - i
    {
        let v_clone = v.clone();
        result.push(v_clone);

        assert(result[i as int]@ == v@) by (ext_equal) {
            assert(v.clone()@ == v@) by {
                vstd::vec::clone_ensures_seq_eq(&v);
            }
            assert(result.last()@ == v.clone()@);
            assert(result.last()@ == v@);
        };
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}