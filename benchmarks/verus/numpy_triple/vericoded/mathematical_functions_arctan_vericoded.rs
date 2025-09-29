// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn arctan_approximation(x: i32) -> (result: i32)
    requires true,
    ensures
        result >= -2 && result <= 2,
        (x > 0 ==> result >= 0),
        (x < 0 ==> result <= 0),
        (x == 0 ==> result == 0),
        (x > 10 ==> result >= 1),
        (x < -10 ==> result <= -1)
{
    if x == 0 {
        0
    } else if x > 10 {
        2
    } else if x < -10 {
        -2
    } else if x > 0 {
        1
    } else {
        -1
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
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                result[j] >= -2 && result[j] <= 2 &&
                (x[j] > 0 ==> result[j] >= 0) &&
                (x[j] < 0 ==> result[j] <= 0) &&
                (x[j] == 0 ==> result[j] == 0) &&
                (x[j] > 10 ==> result[j] >= 1) &&
                (x[j] < -10 ==> result[j] <= -1)
            }
        decreases x.len() - i
    {
        let approx = arctan_approximation(x[i]);
        result.push(approx);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}