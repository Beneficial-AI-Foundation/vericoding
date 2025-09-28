// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Simplified copy_sign implementation and added proper type casting */
fn copy_sign(magnitude: i8, sign: i8) -> (result: i8)
    ensures
        sign >= 0 ==> result >= 0,
        sign < 0 ==> result < 0,
        (if result >= 0 { result as int } else { -(result as int) }) == (if magnitude >= 0 { magnitude as int } else { -(magnitude as int) }),
{
    let abs_val = if magnitude >= 0 { magnitude } else { -magnitude };
    if sign >= 0 {
        abs_val
    } else {
        -abs_val
    }
}
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
/* code modified by LLM (iteration 5): Fixed syntax error in invariant condition */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (x2@[j] >= 0 ==> result@[j] >= 0) && (x2@[j] < 0 ==> result@[j] < 0) &&
                ((if result@[j] >= 0 { result@[j] as int } else { -(result@[j] as int) }) == 
                 (if x1@[j] >= 0 { x1@[j] as int } else { -(x1@[j] as int) }))
            },
        decreases x1.len() - i,
    {
        result.push(copy_sign(x1[i], x2[i]));
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}