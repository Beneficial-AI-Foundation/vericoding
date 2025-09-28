// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn multiply(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == (x1[i] as int) * (x2[i] as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed arithmetic overflow and precondition issues by using int for multiplication and asserting product fits in i8 range */
{
    let mut result = Vec::<i8>::new();
    for j in 0..x1.len()
        invariant
            result.len() == j,
        decreases x1.len() - j,
    {
        let prod: int = (x1[j] as int) * (x2[j] as int);
        assert(prod >= -128 && prod <= 127);
        result.push(prod as i8);
    }
    result
}
// </vc-code>


}
fn main() {}