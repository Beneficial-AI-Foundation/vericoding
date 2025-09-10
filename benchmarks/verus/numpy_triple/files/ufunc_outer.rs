use vstd::prelude::*;

verus! {

spec fn apply_binary_op(op_id: int, x: f64, y: f64) -> f64;

fn outer(op_id: int, a: Vec<f64>, b: Vec<f64>) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == b.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> 
            result[i][j] == apply_binary_op(op_id, a[i], b[j]),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==>
            exists|ai: f64, bj: f64| ai == a[i] && bj == b[j] && result[i][j] == apply_binary_op(op_id, ai, bj)
{
    assume(false);
    unreached()
}

}
fn main() {}