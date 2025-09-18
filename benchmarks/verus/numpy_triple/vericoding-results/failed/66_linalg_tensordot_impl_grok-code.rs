// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Changed return type to i32 to avoid using ghost types in executable code, removed 'as int' casts, using i32 arithmetic, and updated ensures to cast result to int for comparison with spec. */fn dot_product_exec(a: &Vec<i32>, b: &Vec<i32>, i: usize) -> i32
    requires
        a.len() == b.len(),
        i <= a.len()
    ensures
        ((result as int) == dot_product_recursive(a@, b@, i as nat)),
        result >= i32::MIN as int && result <= i32::MAX as int
    decreases a.len() - i
{
    if i == a.len() {
        0
    } else {
        a[i] * b[i] + dot_product_exec(a, b, i + 1)
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
    /* code modified by LLM (iteration 5): Directly called the modified helper function and returned the i32 result, removed the int casting since helper now returns i32, removed proof block as range is now included in helper ensures. */
    let result = dot_product_exec(&a, &b, 0);
    result
}
// </vc-code>

}
fn main() {}