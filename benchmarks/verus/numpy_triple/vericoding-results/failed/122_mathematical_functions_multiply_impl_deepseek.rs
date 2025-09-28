// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Fixed ghost code usage by moving to spec functions */
#[verifier::spec]
fn multiply_spec_index(x1: Seq<i8>, x2: Seq<i8>, i: int) -> (v: int)
    requires 0 <= i < x1.len(),
    ensures v == (x1[i] as int) * (x2[i] as int),
{
    (x1[i] as int) * (x2[i] as int)
}

fn compute_product(x1_val: i8, x2_val: i8) -> (product: i8)
    ensures product as int == (x1_val as int) * (x2_val as int),
{
    ((x1_val as i32) * (x2_val as i32)) as i8
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
    /* code modified by LLM (iteration 5): Fixed compilation by using concrete i32 operations */
    let mut result = Vec::new();
    let n = x1.len();
    let mut i = 0;
    
    while i < n
        invariant
            result.len() == i,
            i <= n,
            forall|j: int| 0 <= j < i ==> result@[j] as int == multiply_spec_index(x1@, x2@, j),
    {
        let product = compute_product(x1[i], x2[i]);
        result.push(product);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}