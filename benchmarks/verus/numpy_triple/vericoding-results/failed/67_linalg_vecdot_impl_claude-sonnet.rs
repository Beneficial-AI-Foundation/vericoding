// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn dot_product_loop_inv(x1: Seq<i32>, x2: Seq<i32>, i: int, acc: int) -> bool {
    0 <= i <= x1.len() &&
    x1.len() == x2.len() &&
    acc == dot_product_spec(x1.take(i), x2.take(i))
}

/* helper modified by LLM (iteration 5): fixed take method to use int instead of nat */
proof fn dot_product_commutative(x1: Seq<i32>, x2: Seq<i32>)
    requires x1.len() == x2.len()
    ensures dot_product_spec(x1, x2) == dot_product_spec(x2, x1)
    decreases x1.len()
{
    if x1.len() == 0 {
    } else {
        dot_product_commutative(x1.skip(1), x2.skip(1));
    }
}

spec fn safe_multiply(a: i32, b: i32) -> bool {
    let result = a as int * b as int;
    result >= i32::MIN as int && result <= i32::MAX as int
}

spec fn safe_add(a: i32, b: i32) -> bool {
    let result = a as int + b as int;
    result >= i32::MIN as int && result <= i32::MAX as int
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
    /* code modified by LLM (iteration 5): added overflow checks for arithmetic operations */
    let mut result: i32 = 0;
    let mut i: usize = 0;
    
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            x1.len() == x2.len(),
            result as int == dot_product_spec(x1@.take(i as int), x2@.take(i as int)),
            forall|j: int| 0 <= j < i ==> safe_multiply(x1@[j], x2@[j]),
            forall|j: int| 0 <= j < i ==> safe_add(result, x1@[j] * x2@[j])
        decreases x1.len() - i
    {
        assert(safe_multiply(x1[i], x2[i]));
        let product = x1[i] * x2[i];
        assert(safe_add(result, product));
        result = result + product;
        i = i + 1;
    }
    
    proof {
        assert(x1@.take(x1.len() as int) =~= x1@);
        assert(x2@.take(x2.len() as int) =~= x2@);
        dot_product_commutative(x1@, x2@);
    }
    
    result
}
// </vc-code>

}
fn main() {}