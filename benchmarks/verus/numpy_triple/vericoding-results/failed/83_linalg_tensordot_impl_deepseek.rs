// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed return type and removed problematic zip/map operation */
spec fn sum(s: Seq<i32>) -> i32
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (s[0] as int) + sum(s.subrange(1, s.len() as int))
    }
}

proof fn dot_product_recursive_correct(a: Seq<i32>, b: Seq<i32>, i: nat)
    requires
        i <= a.len(),
        a.len() == b.len(),
    ensures dot_product_recursive(a, b, i) == sum(a.subrange(i as int, a.len() as int).map(|x, idx| x * b[i as int + idx]))
    decreases a.len() - i
{
    if i < a.len() {
        dot_product_recursive_correct(a, b, i + 1);
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
    /* code modified by LLM (iteration 5): Simplified implementation using direct loop */
    let mut sum_val: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            sum_val == dot_product_recursive(a@, b@, i as nat),
        decreases a.len() - i
    {
        sum_val = sum_val + a[i] * b[i];
        i = i + 1;
    }
    
    sum_val
}
// </vc-code>

}
fn main() {}