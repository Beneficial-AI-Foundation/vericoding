// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn abs_value(x: i8) -> (abs: int)
    ensures
        if x >= 0 { abs == x as int } else { abs == -(x as int) },
{
    if x >= 0 {
        x as int
    } else {
        -(x as int)
    }
}

fn copy_sign_helper(magnitude: int, sign_source: i8) -> (result: i8)
    requires
        if magnitude >= 0 { magnitude <= 127 } else { magnitude >= -128 },
    ensures
        if sign_source >= 0 { result as int == magnitude } else { result as int == -magnitude },
        if sign_source >= 0 { result >= 0 } else { result < 0 },
        abs_value(result) == abs_value(magnitude as i8),
{
    if sign_source >= 0 {
        magnitude as i8
    } else {
        (-magnitude) as i8
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
{
    /* code modified by LLM (iteration 2): fixed type conversion issues */
    let mut result = Vec::new();
    let n = x1.len();
    
    for i in 0..n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                (x2@[j] >= 0 ==> result@[j] as int == if x1@[j] >= 0 { x1@[j] as int } else { -(x1@[j] as int) }) &&
                (x2@[j] < 0 ==> result@[j] as int == if x1@[j] >= 0 { -(x1@[j] as int) } else { x1@[j] as int }) &&
                abs_value(result@[j]) == abs_value(x1@[j]) &&
                (x2@[j] >= 0 ==> result@[j] >= 0) &&
                (x2@[j] < 0 ==> result@[j] < 0)
            },
        decreases n - i
    {
        let magnitude = abs_value(x1@[i]);
        let new_value = copy_sign_helper(magnitude, x2@[i]);
        result.push(new_value);
    }
    
    result
}
// </vc-code>


}
fn main() {}