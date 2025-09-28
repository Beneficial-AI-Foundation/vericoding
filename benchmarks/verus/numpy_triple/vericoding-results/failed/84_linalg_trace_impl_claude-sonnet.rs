// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added missing decreases clause to fix compilation error */
fn is_square_matrix(x: &Vec<Vec<f32>>) -> (result: bool)
    requires
        x@.len() > 0,
    ensures
        result == (forall|i: int| 0 <= i < x@.len() ==> x@[i].len() == x@.len()),
{
    let mut j = 0;
    while j < x.len()
        invariant
            0 <= j <= x@.len(),
            forall|k: int| 0 <= k < j ==> x@[k as int].len() == x@.len(),
        decreases x@.len() - j
    {
        if x[j].len() != x.len() {
            return false;
        }
        j = j + 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn trace(x: Vec<Vec<f32>>) -> (result: f32)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> x@[i].len() == x@.len(),
    ensures 
        true, /* The trace equals the sum of diagonal elements matrix[i][i] for i in 0..n-1 */
        forall|i: int| 0 <= i < x@.len() ==> x@[i][i] != 0.0f32 ==> result != 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes needed, error was in helper function */
    let mut sum = 0.0f32;
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x@.len(),
            forall|j: int| 0 <= j < x@.len() ==> x@[j].len() == x@.len(),
            forall|j: int| 0 <= j < i ==> (x@[j as int][j as int] != 0.0f32 ==> sum != 0.0f32),
            i < x@.len() ==> i < x@[i as int].len(),
        decreases x@.len() - i
    {
        proof {
            assert(i < x@.len());
            assert(x@[i as int].len() == x@.len());
            assert(i < x@[i as int].len());
        }
        let diagonal_val = x[i][i];
        sum = sum + diagonal_val;
        i = i + 1;
    }
    sum
}
// </vc-code>


}
fn main() {}