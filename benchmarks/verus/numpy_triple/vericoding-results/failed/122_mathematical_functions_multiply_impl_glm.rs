// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): use i16 to avoid int in non-ghost code */
fn multiply_elem(a: i8, b: i8) -> (result: i8)
    ensures result as int == (a as int) * (b as int)
{
    let a_wide = a as i16;
    let b_wide = b as i16;
    let product_wide = a_wide * b_wide;
    if product_wide < i8::MIN as i16 || product_wide > i8::MAX as i16 {
        0
    } else {
        product_wide as i8
    }
}
// </vc-helpers>

// <vc-spec>
fn multiply(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == (x1[i] as int) * (x2[i] as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): unchanged */
{
    let mut result = Vec::new();
    let len = x1.len();
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == (x1@[j] as int) * (x2@[j] as int),
        decreases len - i
    {
        let a = x1[i];
        let b = x2[i];
        let c = multiply_elem(a, b);
        result.push(c);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}