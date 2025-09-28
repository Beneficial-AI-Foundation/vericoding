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
{
    /* code modified by LLM (iteration 5): Added arithmetic overflow check and assertion to fix verification */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x1@[j] - x2@[j],
            x1.len() == x2.len(),
        decreases x1.len() - i
    {
        // Check for arithmetic overflow before subtraction
        assert(x1@[i as int] - x2@[i as int] >= -128);
        assert(x1@[i as int] - x2@[i as int] <= 127);
        
        let diff = x1[i] - x2[i];
        result.push(diff);
        
        assert(result.len() == i + 1);
        assert(result@[i as int] == x1@[i as int] - x2@[i as int]);
        
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}