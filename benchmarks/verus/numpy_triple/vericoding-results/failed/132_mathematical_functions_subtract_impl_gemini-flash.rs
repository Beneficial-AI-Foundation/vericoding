// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn subtract(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result@[i] == x1@[i] - x2@[i],
        /* Sanity check: subtracting zero preserves the original value */
        forall|i: int| 0 <= i < result.len() && x2@[i] == 0 ==> result@[i] == x1@[i],
        /* Sanity check: subtracting a value from itself yields zero */
        forall|i: int| 0 <= i < result.len() && x1@[i] == x2@[i] ==> result@[i] == 0,
        /* Anti-commutativity property */
        forall|i: int| 0 <= i < result.len() ==> result@[i] == -(x2@[i] - x1@[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The previous iteration had compilation errors regarding mismatched types due to incorrect indexing within the forall statement. Specifically, the subtraction operation `x1@[j as usize] - x2@[j as usize]` expects `i8` operands, but was implicitly receiving values from indexing `x1` and `x2` that were `i8`, but the indices themselves `j as usize` were causing issues. The fix involves explicitly casting the elements from `i8` vectors to `int` within the `forall` statement to align with the Verus `int` type for arithmetic operations in specifications, while keeping the indexing as `usize` for `Vec` access. */
{
    let len: usize = x1.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < len
        invariant
            result.len() == i,
            i <= len,
            forall|j: int| 0 <= j < i as int ==> result@[j] == (x1@[j as usize] as int - x2@[j as usize] as int) as i8,
            // Adding an explicit requirement for x1.len() and x2.len() to be equal for the duration of the loop.
            x1.len() == x2.len(),
        decreases len - i
    {
        result.push(x1[i] - x2[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}