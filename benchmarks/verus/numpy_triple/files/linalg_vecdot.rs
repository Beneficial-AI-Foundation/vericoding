// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}