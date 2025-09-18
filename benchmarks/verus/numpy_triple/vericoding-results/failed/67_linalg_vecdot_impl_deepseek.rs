// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn dot_product_symmetric_lemma(x1: Seq<i32>, x2: Seq<i32>)
    ensures dot_product_spec(x1, x2) == dot_product_spec(x2, x1)
    decreases x1.len()
{
    if x1.len() == 0 || x1.len() != x2.len() {
        // Base case: empty or mismatched lengths
    } else {
        assert(x1[0] * x2[0] == x2[0] * x1[0]);
        dot_product_symmetric_lemma(x1.skip(1), x2.skip(1));
    }
}

fn dot_product_recursive(x1: &Vec<i32>, x2: &Vec<i32>, index: usize) -> (result: i32)
    requires
        index <= x1.len(),
        x1.len() == x2.len(),
    ensures
        result as int == dot_product_spec(x1@.subrange(index as int, x1.len() as int), x2@.subrange(index as int, x2.len() as int))
    decreases x1.len() - index
{
    if index == x1.len() {
        0
    } else {
        let current = (x1[index] as i32) * (x2[index] as i32);
        let rest = dot_product_recursive(x1, x2, index + 1);
        current + rest
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
/* code modified by LLM (iteration 5): fixed integer casting and type issues */
{
    proof {
        dot_product_symmetric_lemma(x1@, x2@);
    }
    
    let result = dot_product_recursive(&x1, &x2, 0);
    result
}
// </vc-code>

}
fn main() {}