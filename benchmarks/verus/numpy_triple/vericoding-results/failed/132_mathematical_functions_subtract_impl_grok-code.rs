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
/* code modified by LLM (iteration 2): Fixed runtime indexing of Vec elements using [index] instead of @[index] */
{
    let mut result = Vec::<i8>::new();
    let mut index = 0;
    while index < x1.len()
        invariant
            result.len() == index,
            forall|k: int| 0 <= k < index ==> result@[k] == x1@[k] - x2@[k],
        decreases x1.len() - index,
    {
        result.push(x1[index] - x2[index]);
        index = index + 1;
    }
    result
}
// </vc-code>


}
fn main() {}