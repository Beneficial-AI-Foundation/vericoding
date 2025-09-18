// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): removed failing assertions to let verifier prove postconditions automatically */
fn bitwise_and_helper(a: u32, b: u32) -> (result: u32)
    ensures 
        result == (a & b) &&
        (a & b) == (b & a) &&
        (a & 0) == 0 &&
        (a & a) == a &&
        result <= a && result <= b
{
    a & b
}
// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: &Vec<u32>, x2: &Vec<u32>) -> (result: Vec<u32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == (x1[i] & x2[i]) &&

            (x1[i] & x2[i]) == (x2[i] & x1[i]) &&

            (x1[i] & 0) == 0 &&

            (x1[i] & x1[i]) == x1[i] &&

            result[i] <= x1[i] && result[i] <= x2[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed trigger syntax from #![trigger] to #[trigger] */
{
    let n = x1.len();
    let mut result: Vec<u32> = Vec::with_capacity(n);
    for i in 0..n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] result[j], x1[j], x2[j], (x1[j] & x2[j])
                result[j] == (x1[j] & x2[j]) &&
                (x1[j] & x2[j]) == (x2[j] & x1[j]) &&
                (x1[j] & 0) == 0 &&
                (x1[j] & x1[j]) == x1[j] &&
                result[j] <= x1[j] && result[j] <= x2[j]
    {
        result.push(bitwise_and_helper(x1[i], x2[i]));
    }
    result
}
// </vc-code>

}
fn main() {}