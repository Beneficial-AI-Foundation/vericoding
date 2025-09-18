// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define dot_prefix and lemmas relating it to full spec and commutativity */
spec fn dot_prefix(x1: Seq<i32>, x2: Seq<i32>, k: nat) -> int
    decreases k
{
    if k == 0 {
        0
    } else {
        x1[0] * x2[0] + dot_prefix(x1.skip(1), x2.skip(1), k - 1)
    }
}

proof fn dot_prefix_commute(x1: Seq<i32>, x2: Seq<i32>, k: nat)
    requires k <= x1.len() && k <= x2.len()
    ensures dot_prefix(x1, x2, k) == dot_prefix(x2, x1, k)
    decreases k
{
    if k == 0 {
    } else {
        // unfold definitions
        assert(dot_prefix(x1, x2, k) == x1[0] * x2[0] + dot_prefix(x1.skip(1), x2.skip(1), k - 1));
        assert(dot_prefix(x2, x1, k) == x2[0] * x1[0] + dot_prefix(x2.skip(1), x1.skip(1), k - 1));
        // recursive step
        dot_prefix_commute(x1.skip(1), x2.skip(1), k - 1);
        // combine commutativity of tails with commutativity of head multiplication
        assert(x1[0] * x2[0] + dot_prefix(x1.skip(1), x2.skip(1), k - 1) == x2[0] * x1[0] + dot_prefix(x2.skip(1), x1.skip(1), k - 1));
    }
}

proof fn dot_prefix_eq_dot_product_spec(x1: Seq<i32>, x2: Seq<i32>, k: nat)
    requires k == x1.len() && k == x2.len()
    ensures dot_prefix(x1, x2, k) == dot_product_spec(x1, x2)
    decreases k
{
    if k == 0 {
    } else {
        // unfold definitions
        assert(dot_prefix(x1, x2, k) == x1[0] * x2[0] + dot_prefix(x1.skip(1), x2.skip(1), k - 1));
        assert(dot_product_spec(x1, x2) == x1[0] * x2[0] + dot_product_spec(x1.skip(1), x2.skip(1)));
        // recursive step on tails (length decreases by 1)
        dot_prefix_eq_dot_product_spec(x1.skip(1), x2.skip(1), k - 1);
        // combine
        assert(x1[0] * x2[0] + dot_prefix(x1.skip(1), x2.skip(1), k - 1) == x1[0] * x2[0] + dot_product_spec(x1.skip(1), x2.skip(1)));
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
    /* code modified by LLM (iteration 5): iterative dot product with prefix-spec-based invariant */
    let n = x1.len();
    let mut i: usize = 0;
    let mut acc: i32 = 0;
    while i < n
        invariant i <= n
        invariant (acc as int) == dot_prefix(x1@, x2@, i as nat)
        decreases n - i
    {
        let xi = x1[i];
        let yi = x2[i];
        acc = acc + xi * yi;
        i = i + 1;
    }
    let result = acc;
    proof {
        assert((result as int) == dot_prefix(x1@, x2@, n as nat));
        // result equals full dot product spec for x1,x2
        dot_prefix_eq_dot_product_spec(x1@, x2@, n as nat);
        assert((result as int) == dot_product_spec(x1@, x2@));
        // show result equals dot product spec for x2,x1 as well
        dot_prefix_commute(x1@, x2@, n as nat);
        assert((result as int) == dot_prefix(x2@, x1@, n as nat));
        dot_prefix_eq_dot_product_spec(x2@, x1@, n as nat);
        assert((result as int) == dot_product_spec(x2@, x1@));
    }
    result
}

// </vc-code>

}
fn main() {}