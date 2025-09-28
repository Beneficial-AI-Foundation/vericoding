// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    requires c1.len() == c2.len(),
    ensures 
        result.len() == c1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == c1[i] as int - c2[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut result = Vec::new();
    let n = c1.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == c1.len(),
            n == c2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == c1[j] as int - c2[j] as int,
        decreases n - i
    {
        let diff = c1[i] - c2[i];
        result.push(diff);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}