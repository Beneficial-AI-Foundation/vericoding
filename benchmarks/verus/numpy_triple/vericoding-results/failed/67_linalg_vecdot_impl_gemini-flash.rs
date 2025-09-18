// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unused helper 'length_spec' as it was not relevant to the current `vecdot` implementation and caused no-method-found errors on subsequence calls */
// </vc-helpers>

// <vc-spec>
spec fn dot_product_spec(x1: Seq<i32>, x2: Seq<i32>) -> int
    decreases x1.len()
{
    if x1.len() == 0 || x1.len() != x2.len() {
        0
    } else {
        x1[0] * x2[0] + dot_product_spec(x1.skip(1), x2.skip(1))
    }
}

fn vecdot(x1: Vec<i32>, x2: Vec<i32>) -> (result: i32)
    requires x1.len() == x2.len(),
    ensures 
        result as int == dot_product_spec(x1@, x2@),
        result as int == dot_product_spec(x2@, x1@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed mismatch types. 'subrange' method expects 'int' for start and 'nat' for end. Changed 'i as nat' to 'i as int' for the start range. */
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;

    while i < x1.len()
        invariant 
            x1.len() == x2.len(),
            0 <= i && i <= x1.len(),
            sum as int == dot_product_spec(x1@.subrange(0, i as nat), x2@.subrange(0, i as nat))
    {
        sum = sum + x1[i] * x2[i];
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}