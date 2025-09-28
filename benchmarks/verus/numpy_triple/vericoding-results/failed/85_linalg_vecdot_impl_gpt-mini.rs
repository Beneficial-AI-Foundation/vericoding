// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed proof blocks and used direct asserts to prove commutativity */
proof fn dot_product_spec_comm(x1: Seq<i32>, x2: Seq<i32>)
    requires
        x1.len() == x2.len(),
    ensures
        dot_product_spec(x1, x2) == dot_product_spec(x2, x1),
    decreases x1.len()
{
    if x1.len() == 0 {
        assert(dot_product_spec(x1, x2) == 0);
        assert(dot_product_spec(x2, x1) == 0);
    } else {
        let a: i32 = x1[0];
        let b: i32 = x2[0];
        dot_product_spec_comm(x1.skip(1), x2.skip(1));
        assert(dot_product_spec(x1, x2) == a * b + dot_product_spec(x1.skip(1), x2.skip(1)));
        assert(dot_product_spec(x2, x1) == b * a + dot_product_spec(x2.skip(1), x1.skip(1)));
        assert(a * b == b * a);
        assert(dot_product_spec(x1.skip(1), x2.skip(1)) == dot_product_spec(x2.skip(1), x1.skip(1)));
        assert(dot_product_spec(x1, x2) == dot_product_spec(x2, x1));
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
/* code modified by LLM (iteration 5): iterative dot product with invariant and calling proof helper */
{
    let n_usize: usize = x1.len();
    let mut i_usize: usize = 0;
    let mut acc: i32 = 0;
    while i_usize < n_usize
        invariant
            i_usize <= n_usize,
            acc as int + dot_product_spec(x1@.skip(i_usize as int), x2@.skip(i_usize as int)) == dot_product_spec(x1@, x2@),
        decreases (n_usize - i_usize) as nat
    {
        acc = acc + x1[i_usize] * x2[i_usize];
        i_usize = i_usize + 1;
    }
    dot_product_spec_comm(x1@, x2@);
    acc
}
// </vc-code>

}
fn main() {}