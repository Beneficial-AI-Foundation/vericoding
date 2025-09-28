// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn compute_dot_product(a: Vec<i32>, b: Vec<i32>) -> (result: i32)
    requires
        a.len() == b.len(),
    ensures
        result == dot_product(a@, b@),
{
    /* helper modified by LLM (iteration 5): removed ghost type usage in executable code */
    let mut sum = 0;
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            i <= b.len(),
            sum == dot_product_recursive(a@, b@, 0) - dot_product_recursive(a@, b@, i as nat),
        decreases a.len() - i
    {
        let a_val = a[i];
        let b_val = b[i];
        sum = sum + (a_val * b_val);
        i = i + 1;
    }
    sum
}
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
    /* code modified by LLM (iteration 5): no changes needed */
    compute_dot_product(a, b)
}
// </vc-code>

}
fn main() {}