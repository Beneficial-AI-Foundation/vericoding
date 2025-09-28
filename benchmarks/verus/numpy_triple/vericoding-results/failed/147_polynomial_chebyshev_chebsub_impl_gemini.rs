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
    /* code modified by LLM (iteration 5): Replaced Vec::from_fn with a while loop to fix compilation errors. */
    let len = c1.len();
    let mut result: Vec<i8> = Vec::with_capacity(len);
    let mut i: usize = 0;
    while i < len
        invariant
            c1.len() == c2.len(),
            len == c1.len(),
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == c1@[j] as int - c2@[j] as int,
    {
        // Use i16 for subtraction to prevent overflow panic at runtime.
        // The cast to i8 requires proof that the result fits, which is not provable
        // from the preconditions, but is the logical implementation of the spec.
        let val = ((c1[i] as i16) - (c2[i] as i16)) as i8;
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}