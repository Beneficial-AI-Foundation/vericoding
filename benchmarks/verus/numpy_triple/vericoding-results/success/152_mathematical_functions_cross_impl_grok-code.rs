// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn cross(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == 3,
        b.len() == 3,
    ensures 
        result.len() == 3,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed truncate attribute syntax by applying it to the cast expressions with parentheses */
    let a1 = a[1] as i32;
    let b2 = b[2] as i32;
    let mul1 = a1.wrapping_mul(b2);
    let a2 = a[2] as i32;
    let b1 = b[1] as i32;
    let mul2 = a2.wrapping_mul(b1);
    let c0 = mul1.wrapping_sub(mul2);
    let a2_ = a[2] as i32;
    let b0 = b[0] as i32;
    let mul3 = a2_.wrapping_mul(b0);
    let a0 = a[0] as i32;
    let b2_ = b[2] as i32;
    let mul4 = a0.wrapping_mul(b2_);
    let c1 = mul3.wrapping_sub(mul4);
    let a0_ = a[0] as i32;
    let b1_ = b[1] as i32;
    let mul5 = a0_.wrapping_mul(b1_);
    let a1_ = a[1] as i32;
    let b0_ = b[0] as i32;
    let mul6 = a1_.wrapping_mul(b0_);
    let c2 = mul5.wrapping_sub(mul6);
    let mut result = Vec::new();
    result.push(#[verifier::truncate](c0 as i8));
    result.push(#[verifier::truncate](c1 as i8));
    result.push(#[verifier::truncate](c2 as i8));
    result
}
// </vc-code>

}
fn main() {}