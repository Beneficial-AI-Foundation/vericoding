use vstd::prelude::*;

verus! {

spec fn min_usize(a: usize, b: usize) -> usize {
    if a <= b { a } else { b }
}

fn matrix_rank(A: Vec<Vec<f32>>) -> (result: usize)
    requires 
        A.len() > 0,
        A[0].len() > 0,
        forall|i: int| 0 <= i < A.len() ==> #[trigger] A[i].len() == A[0].len(),
    ensures
        result <= min_usize(A.len(), A[0].len()),

        (forall|i: int, j: int| 0 <= i < A.len() && 0 <= j < A[0].len() ==> #[trigger] A[i][j] == 0.0f32) ==> result == 0,

        (A.len() == A[0].len() && forall|i: int, j: int| 0 <= i < A.len() && 0 <= j < A[0].len() ==> #[trigger] A[i][j] == (if i == j { 1.0f32 } else { 0.0f32 })) ==> result == A.len(),

        (A.len() == 1 && A[0].len() == 1) ==> ((result == 1) <==> (A[0][0] != 0.0f32)),
{
    assume(false);
    unreached()
}

}
fn main() {}