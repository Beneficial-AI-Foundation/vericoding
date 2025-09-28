// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn below_zero(operations: &Vec<i32>) -> (result: (Vec<i32>, bool))
    ensures
        result.0.len() == operations.len() + 1,
        result.0[0] == 0,
        forall|i: int| 0 <= i < operations.len() ==> result.0[i + 1] == result.0[i] + operations[i],
        result.1 == (exists|i: int| 1 <= i < result.0.len() && result.0[i] < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type mismatch in while loop invariant by removing unnecessary cast */
    let mut result_vec: Vec<i32> = Vec::new();
    result_vec.push(0);
    let mut found_negative = false;
    let mut i: usize = 0;
    while i < operations.len()
        invariant
            result_vec.len() == (i as int) + 1,
            result_vec[0] == 0,
            forall|j: int| 0 <= j < (i as int) ==> result_vec[j+1] == result_vec[j] + operations[j],
            found_negative == (exists|j: int| 1 <= j <= (i as int) && result_vec[j] < 0),
        decreases (operations.len() - i) as int
    {
        let next = result_vec[i] + operations[i];
        result_vec.push(next);
        if next < 0 {
            found_negative = true;
        }
        i += 1;
    }
    (result_vec, found_negative)
}
// </vc-code>

}
fn main() {}