// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): create zero-filled Vec of given length */
fn make_zeros(n: usize) -> (res: Vec<i32>)
    ensures
        res.len() == n,
{
    let mut v: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
        decreases n - i
    {
        v.push(0);
        i = i + 1;
    }
    v
}

/* helper modified by LLM (iteration 5): compute sign of an i32 (-1, 0, 1) */
fn sign_i32(x: i32) -> (res: i32)
    ensures
        x > 0 ==> res == 1,
        x == 0 ==> res == 0,
        x < 0 ==> res == -1,
{
    if x > 0 { 1 } else if x < 0 { -1 } else { 0 }
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
    /* code modified by LLM (iteration 5): build zero-filled result matching input length */
    let n: usize = x.len();
    let res: Vec<i32> = make_zeros(n);
    res
}
// </vc-code>


}
fn main() {}