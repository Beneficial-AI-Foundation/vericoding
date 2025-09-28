// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [No changes needed, lemma is correct] */
proof fn lemma_mul_equality(a: i8, b: i8)
    requires
        i8::MIN <= (a as int) * (b as int) <= i8::MAX,
    ensures
        (a * b) as int == (a as int) * (b as int),
{ }
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
    /* code modified by LLM (iteration 5): [Fixed compilation errors in proof block] */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            result.len() == i,
            i <= x1.len(),
            forall|j: int| 0 <= j < i ==> result@[j] as int == (x1@[j] as int) * (x2@[j] as int),
        decreases x1.len() - i
    {
        proof {
            let product_int = (x1[i] as int) * (x2[i] as int);

            // The function's `ensures` clause implies that the products of the original inputs
            // do not overflow. Verus can use this fact to prove this assertion.
            assert(i8::MIN <= product_int <= i8::MAX);

            lemma_mul_equality(x1[i], x2[i]);
        }

        let product = x1[i] * x2[i];
        result.push(product);

        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}