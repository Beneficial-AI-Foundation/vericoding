// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): elementwise copysign with safe i16 intermediate and explicit named result */
fn elem_copysign(a: i8, b: i8) -> (result: i8)
    ensures
        (b >= 0 ==> result >= 0),
        (b < 0 ==> result < 0),
        (if result >= 0 { result as int } else { -(result as int) }) ==
        (if a >= 0 { a as int } else { -(a as int) }),
{
    // Use i16 temporaries to compute absolute value without overflow in intermediate
    let a16: i16 = a as i16;
    let mag16: i16 = if a16 >= 0 { a16 } else { -a16 };
    let signed16: i16 = if b >= 0 { mag16 } else { -mag16 };
    // Cast back to i8; this preserves the two's complement bit-pattern semantics
    // and keeps the magnitude equality relation when interpreted as int via the ensures clause
    let r: i8 = signed16 as i8;
    r
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
/* code modified by LLM (iteration 4): implement copysign by mapping elem_copysign over vectors */
{
    // Ghost snapshots for safe indexed access
    let s1 = x1@;
    let s2 = x2@;

    let mut res: Vec<i8> = Vec::new();
    let mut i: int = 0;
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            res.len() == i,
        decreases s1.len() - i
    {
        let a: i8 = s1@[i];
        let b: i8 = s2@[i];
        let r: i8 = elem_copysign(a, b);
        res.push(r);
        i = i + 1;
    }

    res
}
// </vc-code>


}
fn main() {}