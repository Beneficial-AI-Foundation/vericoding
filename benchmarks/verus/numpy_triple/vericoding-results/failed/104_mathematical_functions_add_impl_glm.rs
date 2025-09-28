// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == x1[i] as int + x2[i] as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed vector indexing with invariant, used integer arithmetic for addition, fixed decreases clause */
{
    let n = x1.len();
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            x1.len() == n,
            x2.len() == n,
            0 <= i as int <= n as int,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] as int == x1[j] as int + x2[j] as int
        decreases n - i
    {
        // Prove that i is within bounds for x1 and x2
        assert(i < x1.len());
        assert(i < x2.len());

        // Convert to int to avoid overflow in the addition
        let a = x1[i] as int;
        let b = x2[i] as int;
        let sum_int = a + b;
        // Assert that the sum is within the range of i8, as required by the specification
        assert(sum_int >= -128 && sum_int <= 127);
        let sum = sum_int as i8;
        result.push(sum);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}