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
    /* code modified by LLM (iteration 5): added decreases clause for while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < c1.len()
        invariant
            i <= c1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == c1@[j] as int - c2@[j] as int,
        decreases c1.len() - i
    {
        proof {
            let diff = c1@[i as int] as int - c2@[i as int] as int;
            assert(-128 <= diff <= 127);
        }
        let diff_i8 = (c1[i] as i16 - c2[i] as i16) as i8;
        result.push(diff_i8);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}