// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed to proof function to resolve compilation error with int types in non-ghost code */
proof fn lemma_dot_commutative(x1: Seq<i32>, x2: Seq<i32>)
    requires x1.len() == x2.len(),
    ensures dot_product_spec(x1, x2) == dot_product_spec(x2, x1),
    decreases x1.len()
{
    if x1.len() == 0 {
    } else {
        lemma_dot_commutative(x1.skip(1), x2.skip(1));
        assert(dot_product_spec(x1, x2) == (x1[0] as int) * (x2[0] as int) + dot_product_spec(x1.skip(1), x2.skip(1)));
        assert(dot_product_spec(x2, x1) == (x2[0] as int) * (x1[0] as int) + dot_product_spec(x2.skip(1), x1.skip(1)));
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
{
    /* code modified by LLM (iteration 5): final loop-based implementation with proper invariants and commutative proof */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    if x1@.len() == 0 {
        proof { lemma_dot_commutative(x1@, x2@); }
        return 0;
    }
    while i < x1.len()
        invariant
            sum as int == dot_product_spec(x1@.take((i as int)), x2@.take((i as int))),
            0 <= (i as int) && (i as int) <= x1@.len(),
        decreases x1.len() - i as usize
    {
        sum = sum + (x1[i] * x2[i]);
        i = i + 1;
    }
    proof { lemma_dot_commutative(x1@, x2@); }
    return sum;
}
// </vc-code>

}
fn main() {}