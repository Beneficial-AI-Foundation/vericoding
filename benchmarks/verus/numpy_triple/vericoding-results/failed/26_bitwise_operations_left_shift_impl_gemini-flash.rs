// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected return type of `calculate_shifted_value_spec` to `int` instead of `i32` to avoid `i32` to `int` mismatch for `pow` function result. `pow` returns `int`, while `x1 * (int)` also returns `int`. */
spec fn calculate_shifted_value_spec(val_x1: i32, val_x2: i32) -> int
    requires
        val_x2 >= 0,
{
    val_x1 as int * pow(2, val_x2 as nat)
}
// </vc-helpers>

// <vc-spec>
fn left_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x1[i] * pow(2, x2[i] as nat),
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == 0,
        forall|i: int| 0 <= i < result.len() && x1[i] > 0 && x2[i] > 0 ==> result[i] > x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] < 0 && x2[i] > 0 ==> result[i] < x1[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Addressed compilation errors related to `int` vs `usize` indexing, `i32` * `int` operation, and corrected the call to `calculate_shifted_value_spec`. */
{
    let mut result: Vec<i32> = Vec::new();
    let len: usize = x1.len();
    result.reserve(len);
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i as int <= len as int,
            result.len() == i,
            result.capacity() == len,
            forall|j: int| 0 <= j < i as int ==> result.index(j) && result[j] == calculate_shifted_value_spec(x1[j as usize], x2[j as usize]),
    {
        let val_x1 = x1[i];
        let val_x2 = x2[i];
        let shifted_val: i32 = calculate_shifted_value_spec(val_x1, val_x2) as i32;
        result.push(shifted_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}