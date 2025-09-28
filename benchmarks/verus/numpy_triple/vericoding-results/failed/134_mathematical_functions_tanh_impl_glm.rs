// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added proper initialization and invariants */
fn create_zero_vector(len: usize) -> (result: Vec<i32>)
    ensures result.len() == len,
    forall|i: int| 0 <= i < len ==> result[i] == 0
{
    let mut result = Vec::with_capacity(len);
    let mut i = 0;
    while i < len
        invariant result.len() == i,
        forall|j: int| 0 <= j < i ==> result[j] == 0,
        decreases len - i
    {
        result.push(0);
        i = i + 1;
    }
    result
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
/* code modified by LLM (iteration 4): added explicit type annotation for result vector */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant result.len() == i,
        forall|j: int| 0 <= j < i ==> {
            -1 < result[j] && result[j] < 1 &&
            (x[j] == 0 ==> result[j] == 0) &&
            (x[j] > 0 ==> result[j] > 0) &&
            (x[j] < 0 ==> result[j] < 0) &&
            (x[j] > 0 ==> result[j] > 0 && result[j] < 1) &&
            (x[j] < 0 ==> result[j] < 0 && result[j] > -1)
        },
        decreases x.len() - i
    {
        if x[i] == 0 {
            result.push(0);
        } else if x[i] > 0 {
            result.push(1);
        } else {
            result.push(-1);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}