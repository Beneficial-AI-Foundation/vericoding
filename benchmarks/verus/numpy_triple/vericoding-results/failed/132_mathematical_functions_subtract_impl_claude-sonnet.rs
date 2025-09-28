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
    /* code modified by LLM (iteration 5): added proof block to establish invariant maintenance */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == x1@[j] - x2@[j]
        decreases x1.len() - i
    {
        assert(i < x1.len());
        assert(x1.len() == x2.len());
        assert(i < x2.len());
        
        let val1 = x1[i] as i16;
        let val2 = x2[i] as i16;
        let diff_wide = val1 - val2;
        #[verifier::truncate]
        let diff = diff_wide as i8;
        
        result.push(diff);
        
        proof {
            assert(result.len() == i + 1);
            assert(result@[i as int] == diff);
            assert(diff == x1@[i as int] - x2@[i as int]);
            assert(forall|j: int| 0 <= j < i ==> result@[j] == x1@[j] - x2@[j]);
            assert(forall|j: int| 0 <= j < i + 1 ==> result@[j] == x1@[j] - x2@[j]);
        }
        
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}