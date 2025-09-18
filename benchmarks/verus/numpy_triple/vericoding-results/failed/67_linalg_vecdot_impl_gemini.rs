// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no modification needed */
proof fn dot_product_commutes(x1: Seq<i32>, x2: Seq<i32>)
    requires x1.len() == x2.len()
    ensures dot_product_spec(x1, x2) == dot_product_spec(x2, x1)
    decreases x1.len()
{
    if x1.len() > 0 {
        dot_product_commutes(x1.skip(1), x2.skip(1));
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
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    let mut i: usize = 0;
    let mut sum: i32 = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            x1.len() == x2.len(),
            dot_product_spec(x1@, x2@) == sum as int + dot_product_spec(x1@.skip(i as int), x2@.skip(i as int)),
        decreases x1.len() - i
    {
        let v1 = x1[i];
        let v2 = x2[i];
        sum = sum + v1 * v2;
        i = i + 1;
    }

    proof {
        dot_product_commutes(x1@, x2@);
    }

    sum
}
// </vc-code>

}
fn main() {}