// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemma to split dot product and added proof to existing commutativity lemma */
proof fn dot_product_split(x1: Seq<i32>, x2: Seq<i32>, i: int)
    requires
        0 <= i <= x1.len() as int,
        x1.len() == x2.len(),
    ensures
        dot_product_spec(x1, x2) == dot_product_spec(x1.take(i), x2.take(i)) + dot_product_spec(x1.skip(i), x2.skip(i)),
    decreases x1.len()
{
    if x1.len() > 0 {
        if i > 0 {
            dot_product_split(x1.skip(1), x2.skip(1), i - 1);
        }
    }
}

proof fn dot_product_commutative(x1: Seq<i32>, x2: Seq<i32>)
    requires
        x1.len() == x2.len(),
    ensures
        dot_product_spec(x1, x2) == dot_product_spec(x2, x1),
    decreases x1.len()
{
    if x1.len() > 0 {
        dot_product_commutative(x1.skip(1), x2.skip(1));
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
    /* code modified by LLM (iteration 3): use i64 accumulator and a different invariant to satisfy verifier */
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    let n = x1.len();
    while i < n
        invariant
            0 <= i <= n,
            x1.len() == n,
            x2.len() == n,
            sum as int == dot_product_spec(x1@.take(i as int), x2@.take(i as int)),
        decreases n - i
    {
        proof {
            let i_int = i as int;
            dot_product_split(x1@.take(i_int + 1), x2@.take(i_int + 1), i_int);
        }
        let prod = (x1[i] as i64) * (x2[i] as i64);
        sum = sum + prod;
        i = i + 1;
    }

    proof {
        dot_product_commutative(x1@, x2@);
    }
    
    sum as i32
}
// </vc-code>

}
fn main() {}