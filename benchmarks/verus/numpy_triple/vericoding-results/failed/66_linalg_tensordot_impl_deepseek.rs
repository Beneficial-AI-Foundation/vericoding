// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix nat usage by converting to usize indexing */
fn dot_product_recursive_impl(a: &Vec<i32>, b: &Vec<i32>, i: usize) -> (result: i32)
    requires
        i <= a.len(),
        a.len() == b.len(),
    ensures
        result == dot_product_recursive(a@, b@, i as nat),
    decreases a.len() - i
{
    if i >= a.len() {
        0
    } else {
        let partial = dot_product_recursive_impl(a, b, i + 1);
        a[i] * b[i] + partial
    }
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
/* code modified by LLM (iteration 5): use usize instead of nat for function call */
{
    let result = dot_product_recursive_impl(&a, &b, 0);
    result
}
// </vc-code>

}
fn main() {}