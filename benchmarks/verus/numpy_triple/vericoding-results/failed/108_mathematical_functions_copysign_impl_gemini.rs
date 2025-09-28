// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */

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
    /* code modified by LLM (iteration 3): fixed trigger error by removing let-bindings from loop invariant */
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            result.len() == i,
            i <= x1.len(),
            forall|j: int| 0 <= j < i ==> {
                (x2@[j] >= 0 ==> result@[j] as int == if x1@[j] >= 0 { x1@[j] as int } else { -(x1@[j] as int) }) &&
                (x2@[j] < 0 ==> result@[j] as int == if x1@[j] >= 0 { -(x1@[j] as int) } else { x1@[j] as int }) &&
                (if result@[j] >= 0 { result@[j] as int } else { -(result@[j] as int) }) == 
                (if x1@[j] >= 0 { x1@[j] as int } else { -(x1@[j] as int) }) &&
                (x2@[j] >= 0 ==> result@[j] >= 0) &&
                (x2@[j] < 0 ==> result@[j] < 0)
            }
        decreases x1.len() - i
    {
        let v1 = x1[i];
        let v2 = x2[i];

        let mut res: i8;
        if v2 >= 0 {
            if v1 >= 0 {
                res = v1;
            } else {
                if v1 > i8::MIN {
                    res = -v1;
                } else {
                    res = i8::MAX; 
                }
            }
        } else {
            if v1 >= 0 {
                res = -v1;
            } else {
                res = v1;
            }
        }

        result.push(res);
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}