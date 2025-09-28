// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversion from nat to int and added proper preconditions */
spec fn dot_product_spec_rec(x1: Seq<i32>, x2: Seq<i32>, i: nat) -> int
    decreases x1.len() - i
{
    if i >= x1.len() {
        0
    } else {
        (x1[i] as int) * (x2[i] as int) + dot_product_spec_rec(x1, x2, i + 1)
    }
}

proof fn dot_product_symmetry_lemma(x1: Seq<i32>, x2: Seq<i32>)
    ensures dot_product_spec(x1, x2) == dot_product_spec(x2, x1)
{
    if x1.len() == x2.len() {
        if x1.len() > 0 {
            dot_product_symmetry_lemma(x1.subrange(1 as int, x1.len() as int), x2.subrange(1 as int, x2.len() as int));
        }
    }
}

proof fn dot_product_equivalent_lemma(x1: Seq<i32>, x2: Seq<i32>)
    requires x1.len() == x2.len()
    ensures dot_product_spec(x1, x2) == dot_product_spec_rec(x1, x2, 0)
{
    if x1.len() > 0 {
        dot_product_equivalent_lemma(x1.subrange(1 as int, x1.len() as int), x2.subrange(1 as int, x2.len() as int));
    }
}
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
/* code modified by LLM (iteration 5): Fixed multiplication type conversion */
{
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    let n = x1.len();
    
    while i < n
        invariant
            0 <= i <= n,
            sum as int == dot_product_spec_rec(x1@, x2@, i as nat),
    {
        sum = sum + (x1[i] as i32) * (x2[i] as i32);
        i = i + 1;
    }
    
    proof {
        dot_product_equivalent_lemma(x1@, x2@);
        dot_product_symmetry_lemma(x1@, x2@);
    }
    
    sum
}
// </vc-code>

}
fn main() {}