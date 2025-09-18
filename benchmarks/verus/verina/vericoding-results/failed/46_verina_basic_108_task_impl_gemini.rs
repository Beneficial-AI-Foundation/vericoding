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
    /* code modified by LLM (iteration 2): added decreases clause to the while loop to prove termination */
    let mut result_vec: Vec<i32> = Vec::new();
    result_vec.push(0);

    let mut found_below_zero = false;
    let mut i: usize = 0;
    while i < operations.len()
        invariant
            0 <= i <= operations.len(),
            result_vec.len() == i + 1,
            result_vec.view()[0] == 0,
            forall|j: int| 0 <= j < i ==> result_vec.view()[j + 1] == result_vec.view()[j] + operations.view()[j],
            found_below_zero == (exists|j: int| 1 <= j < result_vec.view().len() && result_vec.view()[j] < 0),
        decreases operations.len() - i,
    {
        let prev_sum = result_vec[i];
        let op = operations[i];
        let next_sum = prev_sum + op;
        result_vec.push(next_sum);

        if next_sum < 0 {
            found_below_zero = true;
        }

        i = i + 1;
    }

    (result_vec, found_below_zero)
}
// </vc-code>

}
fn main() {}