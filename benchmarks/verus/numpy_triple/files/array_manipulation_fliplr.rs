// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn fliplr(m: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> m[i].len() > 0,
        forall|i: int, j: int| 0 <= i < m.len() && 0 <= j < m.len() ==> m[i].len() == m[j].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == m[i].len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==>
            exists|k: int| 0 <= k < m[i].len() && 
                           result[i][j] == m[i][k] && 
                           j + k == (m[i].len() - 1) as int,
        forall|i: int, x: f32| 0 <= i < result.len() ==>
            ((exists|j: int| 0 <= j < m[i].len() && m[i][j] == x) <==> 
             (exists|j: int| 0 <= j < result[i].len() && result[i][j] == x)),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}