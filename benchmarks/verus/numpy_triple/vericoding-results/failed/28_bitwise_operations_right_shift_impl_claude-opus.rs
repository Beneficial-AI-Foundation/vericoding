// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn right_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& (x1[i] >= 0 ==> result[i] == x1[i] / (1i32 << x2[i]))
            &&& (x1[i] < 0 ==> result[i] == x1[i] >> x2[i])
            &&& (x2[i] == 0 ==> result[i] == x1[i])
            &&& (x1[i] > 0 ==> result[i] >= 0)
            &&& (x1[i] < 0 ==> result[i] <= 0)
            &&& (x1[i] == 0 ==> result[i] == 0)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Add assertions to help verify shift preconditions */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            x1.len() == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& (x1[j] >= 0 ==> result[j] == x1[j] / (1i32 << x2[j]))
                &&& (x1[j] < 0 ==> result[j] == x1[j] >> x2[j])
                &&& (x2[j] == 0 ==> result[j] == x1[j])
                &&& (x1[j] > 0 ==> result[j] >= 0)
                &&& (x1[j] < 0 ==> result[j] <= 0)
                &&& (x1[j] == 0 ==> result[j] == 0)
            },
            forall|j: int| 0 <= j < x2.len() ==> x2[j] >= 0,
        decreases x1.len() - i
    {
        // Assert preconditions for shift operations
        assert(x2[i] >= 0);
        assert(x2[i] < 32 ==> 1i32 << x2[i] > 0);
        
        let val = if x2[i] == 0 {
            x1[i]
        } else if x2[i] >= 32 {
            // Shifting by 32 or more bits for i32 results in 0 for positive, -1 for negative
            if x1[i] >= 0 { 0 } else { -1 }
        } else if x1[i] >= 0 {
            // For positive numbers, use division
            // The shift amount is valid (0 <= x2[i] < 32)
            assert(1i32 << x2[i] > 0);
            x1[i] / (1i32 << x2[i])
        } else {
            // For negative numbers, use arithmetic right shift
            x1[i] >> x2[i]
        };
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}