// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn copysign(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            /* Basic behavior: sign copying with magnitude preservation */
            (x2@[i] >= 0 ==> result@[i] as int == if x1@[i] >= 0 { x1@[i] as int } else { -(x1@[i] as int) }) &&
            (x2@[i] < 0 ==> result@[i] as int == if x1@[i] >= 0 { -(x1@[i] as int) } else { x1@[i] as int }) &&
            /* Magnitude preservation property: |result[i]| = |x1[i]| */
            (if result@[i] >= 0 { result@[i] as int } else { -(result@[i] as int) }) == 
            (if x1@[i] >= 0 { x1@[i] as int } else { -(x1@[i] as int) }) &&
            /* Sign copying property: result has same sign as x2 */
            (x2@[i] >= 0 ==> result@[i] >= 0) &&
            (x2@[i] < 0 ==> result@[i] < 0)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to fix verification error */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> {
                (x2@[j] >= 0 ==> result@[j] as int == if x1@[j] >= 0 { x1@[j] as int } else { -(x1@[j] as int) }) &&
                (x2@[j] < 0 ==> result@[j] as int == if x1@[j] >= 0 { -(x1@[j] as int) } else { x1@[j] as int }) &&
                (if result@[j] >= 0 { result@[j] as int } else { -(result@[j] as int) }) == 
                (if x1@[j] >= 0 { x1@[j] as int } else { -(x1@[j] as int) }) &&
                (x2@[j] >= 0 ==> result@[j] >= 0) &&
                (x2@[j] < 0 ==> result@[j] < 0)
            },
        decreases x1.len() - i
    {
        let val = if x2[i] >= 0 {
            if x1[i] >= 0 { x1[i] } else { -x1[i] }
        } else {
            if x1[i] >= 0 { -x1[i] } else { x1[i] }
        };
        
        result.push(val);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}