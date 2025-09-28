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
/* code modified by LLM (iteration 5): Fixed overflow error, added `proof` block for verification. */
{
    let mut result: Vec<i8> = Vec::new();
    result.reserve(c1.len());

    let mut i = 0;
    while i < c1.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == c1[j] as int - c2[j] as int,
            i <= c1.len(),
        decreases c1.len() - i
    {
        let val_c1 = c1[i];
        let val_c2 = c2[i];

        proof {
            assert((val_c1 as int) - (val_c2 as int) >= i8::MIN as int);
            assert((val_c1 as int) - (val_c2 as int) <= i8::MAX as int);
        }

        let sub_val = val_c1 - val_c2;
        result.push(sub_val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}