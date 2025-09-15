// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): empty helper section */
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
/* code modified by LLM (iteration 2): Cast `i` to `int` when indexing `path` to resolve type mismatch */
{
    let mut current_value: i32 = 0;
    let mut path: Vec<i32> = Vec::new();
    let mut below_zero_flag: bool = false;

    path.push(current_value);

    let mut i = 0;
    while i < operations.len()
        invariant
            0 <= i as int <= operations.len() as int,
            path.len() == i + 1,
            path[0] == 0,
            forall|j: int| 0 <= j < i as int ==> path[j + 1] == path[j] + operations[j],
            current_value == path[i as int],
            below_zero_flag == exists|j: int| 1 <= j < path.len() as int && path[j] < 0,
    {
        current_value = current_value + operations[i];
        path.push(current_value);
        if current_value < 0 {
            below_zero_flag = true;
        }
        i = i + 1;
    }

    (path, below_zero_flag)
}
// </vc-code>

}
fn main() {}