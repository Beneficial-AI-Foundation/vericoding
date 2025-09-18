// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added decreases clause for termination */
proof fn lemma_dot_product_commutative(x1: Seq<i32>, x2: Seq<i32>)
    requires x1.len() == x2.len(),
    ensures dot_product_spec(x1, x2) == dot_product_spec(x2, x1)
    decreases x1.len()
{
    if x1.len() == 0 {
    } else {
        assert(x1[0] * x2[0] == x2[0] * x1[0]);
        lemma_dot_product_commutative(x1.skip(1), x2.skip(1));
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
/* code modified by LLM (iteration 5): added decreases clause to while loop */
{
    let n = x1.len();
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while i < n
        invariant 
            0 <= i <= n,
            sum as int == dot_product_spec(x1@.subrange(0, i as int), x2@.subrange(0, i as int)),
        decreases n - i
    {
        sum = sum + x1[i] * x2[i];
        i = i + 1;
    }
    proof {
        lemma_dot_product_commutative(x1@, x2@);
    }
    sum
}
// </vc-code>

}
fn main() {}