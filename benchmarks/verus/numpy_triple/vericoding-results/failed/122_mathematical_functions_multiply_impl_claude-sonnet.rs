// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper to check multiplication bounds */
fn multiply_in_bounds(a: i8, b: i8) -> bool {
    let product = (a as i32) * (b as i32);
    product >= -128 && product <= 127
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
{
    /* code modified by LLM (iteration 5): fixed truncate attribute syntax */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            i <= x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == (x1@[j] as int) * (x2@[j] as int)
        decreases x1.len() - i
    {
        let product = (x1[i] as i32) * (x2[i] as i32);
        result.push((#[verifier::truncate] product) as i8);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}