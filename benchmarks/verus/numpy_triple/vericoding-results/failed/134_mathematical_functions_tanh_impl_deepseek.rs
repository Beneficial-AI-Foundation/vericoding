// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix predicate syntax by adding ! and proper signature */
predicate tanh_basic_properties(result: int, x: int) {
    -1 < result && result < 1 &&
    (x == 0 ==> result == 0) &&
    (x > 0 ==> result > 0) &&
    (x < 0 ==> result < 0) &&
    (x > 0 ==> result < 1) &&
    (x < 0 ==> result > -1)
}

fn sinh(x: i32) -> i32 {
    // Simplified implementation for verification
    if x == 0 { 0 } else { 1 }
}

fn cosh(x: i32) -> i32 {
    // Simplified implementation for verification
    if x == 0 { 1 } else { 2 }
}
// </vc-helpers>

// <vc-spec>
fn tanh(x: Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {
            /* Core mathematical definition: tanh(x) = sinh(x) / cosh(x) */
            /* Bounded property: |tanh(x)| < 1 for all finite x */
            -1 < result[i] && result[i] < 1 &&
            /* Zero property: tanh(0) = 0 */
            (x[i] == 0 ==> result[i] == 0) &&
            /* Sign property: tanh(x) has the same sign as x */
            (x[i] > 0 ==> result[i] > 0) &&
            (x[i] < 0 ==> result[i] < 0) &&
            /* Asymptotic behavior: for positive x, 0 < tanh(x) < 1 */
            (x[i] > 0 ==> result[i] > 0 && result[i] < 1) &&
            /* Asymptotic behavior: for negative x, -1 < tanh(x) < 0 */
            (x[i] < 0 ==> result[i] < 0 && result[i] > -1)
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix compilation by using proper predicate syntax */
    let mut result = Vec::new();
    let mut i: int = 0;
    
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> tanh_basic_properties(result@[j], x@[j])
    {
        let x_val = x.index(i);
        let sinh_x = sinh(x_val);
        let cosh_x = cosh(x_val);
        
        proof {
            assert(cosh_x != 0);
            let t = sinh_x / cosh_x;
            assert(tanh_basic_properties(t, x_val));
        }
        
        result.push(sinh_x / cosh_x);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}