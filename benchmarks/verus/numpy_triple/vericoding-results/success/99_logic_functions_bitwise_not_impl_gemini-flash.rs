// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_bitwise_not(x: Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == -(x[i] + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Changed type annotation for x[i] + 1 to i64 to prevent overflow errors. */
    let mut result = Vec::with_capacity(x.len());
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == -(x[j] + 1) as i32
        decreases x.len() - i
    {
        // Cast x[i] to i64 before adding 1 to prevent overflow, then cast back to i32 after negation
        result.push(-((x[i] as i64) + 1) as i32);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}