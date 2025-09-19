// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn triu(m: &Vec<Vec<f32>>, k: i32) -> (result: Vec<Vec<f32>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> #[trigger] m[i].len() == m[0].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == m[i].len(),
        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < result[i].len() ==>
            #[trigger] result[i][j] == if i as i32 > j as i32 - k { 0.0f32 } else { m[i][j] },
        forall|i: int, j: int|
            0 <= i < result.len() && 0 <= j < result[i].len() && i as i32 <= j as i32 - k ==>
            #[trigger] result[i][j] == m[i][j],
        forall|i: int, j: int|
            0 <= i < result.len() && 0 <= j < result[i].len() && i as i32 > j as i32 - k ==>
            #[trigger] result[i][j] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}