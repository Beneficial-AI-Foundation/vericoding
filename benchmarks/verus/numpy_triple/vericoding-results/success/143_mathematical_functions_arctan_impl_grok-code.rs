// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Corrected indexing in main function by using Vec indexing */
fn approx_arctan(x: i32) -> (result: i32)
    ensures
        -2 <= result && result <= 2 &&
        (x > 0 ==> result >= 0) &&
        (x < 0 ==> result <= 0) &&
        (x == 0 ==> result == 0) &&
        (x > 10 ==> result >= 1) &&
        (x < -10 ==> result <= -1)
{
    if x == 0 {
        0
    } else if x > 0 {
        if x <= 10 {
            1
        } else {
            2
        }
    } else {
        if x >= -10 {
            -1
        } else {
            -2
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn arctan(x: Vec<i32>) -> (result: Vec<i32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            /* Range constraint: arctan(x) ∈ (-π/2, π/2) - simplified for integer domain */
            result[i] >= -2 && result[i] <= 2 &&
            /* Sign property: arctan preserves sign */
            (x[i] > 0 ==> result[i] >= 0) &&
            (x[i] < 0 ==> result[i] <= 0) &&
            (x[i] == 0 ==> result[i] == 0) &&
            /* Monotonicity property for specific cases */
            (x[i] > 10 ==> result[i] >= 1) &&
            (x[i] < -10 ==> result[i] <= -1) &&
            /* Bounded function: |arctan(x)| ≤ 2 for integer approximation */
            result[i] >= -2 && result[i] <= 2
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed indexing error by using x[i] instead of x@[i] in the loop */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i as int <= x.len() &&
            result.len() == i as int &&
            forall|j: int| 0 <= j < i as int ==> (
                -2 <= result@[j] && result@[j] <= 2 &&
                (x@[j] > 0 ==> result@[j] >= 0) &&
                (x@[j] < 0 ==> result@[j] <= 0) &&
                (x@[j] == 0 ==> result@[j] == 0) &&
                (x@[j] > 10 ==> result@[j] >= 1) &&
                (x@[j] < -10 ==> result@[j] <= -1)
            )
        decreases x.len() - i as usize
    {
        result.push(approx_arctan(x[i]));
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}