// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn dot_product_exec(a: &Vec<i32>, b: &Vec<i32>, start: usize) -> (sum: i32)
    decreases a.len() - start
    requires
        a.len() == b.len(),
        start <= a.len(),
    ensures
        sum == dot_product_recursive(a@, b@, start as nat),
{
    if start == a.len() {
        0
    } else {
        a[start] * b[start] + dot_product_exec(a, b, start + 1)
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
{
    let result = dot_product_exec(&a, &b, 0);
    result
}
// </vc-code>

}
fn main() {}