// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn dot_product_commutative(x1: Seq<i32>, x2: Seq<i32>)
    ensures dot_product_spec(x1, x2) == dot_product_spec(x2, x1)
    decreases x1.len()
{
    if x1.len() == 0 || x1.len() != x2.len() {
    } else {
        dot_product_commutative(x1.skip(1), x2.skip(1));
    }
}

proof fn lemma_dot_product_empty(x1: Seq<i32>, x2: Seq<i32>)
    requires x1.len() == 0 || x1.len() != x2.len()
    ensures dot_product_spec(x1, x2) == 0
{
}

proof fn lemma_dot_product_recursive(x1: Seq<i32>, x2: Seq<i32>)
    requires x1.len() > 0 && x1.len() == x2.len()
    ensures dot_product_spec(x1, x2) == x1[0] * x2[0] + dot_product_spec(x1.skip(1), x2.skip(1))
{
}

/* helper modified by LLM (iteration 5): fixed overflow detection logic */
proof fn lemma_safe_addition(a: i32, b: i32)
    requires -2147483648 <= a as int + b as int <= 2147483647
    ensures (a as int + b as int) as i32 as int == a as int + b as int
{
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
    /* code modified by LLM (iteration 5): fixed vector indexing with @ operator */
    if x1.len() == 0 {
        return 0;
    }
    
    let mut result: i32 = 0;
    let mut i = 0;
    
    proof {
        dot_product_commutative(x1@, x2@);
    }
    
    while i < x1.len()
        invariant
            i <= x1.len(),
            x1.len() == x2.len(),
            result as int == dot_product_spec(x1@.take(i as int), x2@.take(i as int)),
            -2147483648 <= result as int <= 2147483647
        decreases x1.len() - i
    {
        let product_ghost: Ghost<int> = Ghost(x1@[i] as int * x2@[i] as int);
        
        proof {
            assert(-2147483648 <= x1@[i] as int <= 2147483647);
            assert(-2147483648 <= x2@[i] as int <= 2147483647);
            assert(-4611686018427387904 <= product_ghost@ <= 4611686014132420609);
            
            if product_ghost@ > 2147483647 - result as int || product_ghost@ < -2147483648 - result as int {
                assert(false); // This should never happen for valid inputs
            }
            
            lemma_safe_addition(result, (product_ghost@ as i32));
        }
        
        result = result + x1[i] * x2[i];
        i = i + 1;
        
        proof {
            assert(x1@.take(i as int) == x1@.take((i-1) as int).push(x1@[(i-1) as int]));
            assert(x2@.take(i as int) == x2@.take((i-1) as int).push(x2@[(i-1) as int]));
        }
    }
    
    proof {
        assert(x1@.take(x1.len() as int) == x1@);
        assert(x2@.take(x2.len() as int) == x2@);
    }
    
    result
}
// </vc-code>

}
fn main() {}