// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unused lemma */
proof fn dot_product_unfold(a: Seq<i32>, b: Seq<i32>, i: nat)
    requires i < a.len() && a.len() == b.len()
    ensures dot_product_recursive(a, b, i) == a[i as int] * b[i as int] + dot_product_recursive(a, b, i + 1)
{
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
    /* code modified by LLM (iteration 5): fixed compilation error and simplified final assertion */
    let mut sum: int = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            axes == 1,
            i <= a.len(),
            sum + dot_product_recursive(a@, b@, i as nat) == dot_product(a@, b@)
        decreases a.len() - i
    {
        proof {
            dot_product_unfold(a@, b@, i as nat);
        }
        sum = sum + (a[i] as int) * (b[i] as int);
        i = i + 1;
    }

    // After the loop, the invariant implies `sum == dot_product(a@, b@)`.
    // The following assertion is required for the cast `sum as i32` to be safe.
    // It is unprovable without preconditions on the input vector values.
    assert(sum >= i32::MIN as int && sum <= i32::MAX as int);

    sum as i32
}
// </vc-code>

}
fn main() {}