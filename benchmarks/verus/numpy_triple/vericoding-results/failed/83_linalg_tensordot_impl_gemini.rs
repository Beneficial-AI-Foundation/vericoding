// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn dot_product_recursive(a: Seq<i32>, b: Seq<i32>, i: nat) -> int
    decreases a.len() - i
{
    if i >= a.len() {
        0
    } else {
        a[i as int] * b[i as int] + dot_product_recursive(a, b, i + 1)
    }
}

spec fn dot_product(a: Seq<i32>, b: Seq<i32>) -> int {
    dot_product_recursive(a, b, 0)
}

fn tensordot(a: Vec<i32>, b: Vec<i32>, axes: usize) -> (result: i32)
    requires 
        a.len() == b.len(),
        axes == 1,
    ensures result == dot_product(a@, b@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): use i32 for computations to fix compilation errors */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            (sum as int) + dot_product_recursive(a@, b@, i as nat) == dot_product(a@, b@),
        decreases a.len() - i
    {
        let term = a[i] * b[i];
        sum = sum + term;
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}