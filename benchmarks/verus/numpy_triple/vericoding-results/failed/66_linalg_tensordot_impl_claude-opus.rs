// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn dot_product_recursive_unroll(a: Seq<i32>, b: Seq<i32>, i: nat)
    requires
        i < a.len(),
        a.len() == b.len(),
    ensures
        dot_product_recursive(a, b, i) == a[i as int] * b[i as int] + dot_product_recursive(a, b, i + 1)
    decreases a.len() - i
{
}

/* helper modified by LLM (iteration 5): fixed parameter type for bounded_mul_add */
proof fn bounded_mul_add(x: i32, y: i32, z: i32)
    requires
        x >= i32::MIN / 2,
        x <= i32::MAX / 2,
        y >= i32::MIN / 2, 
        y <= i32::MAX / 2,
        z >= i32::MIN / 2,
        z <= i32::MAX / 2,
    ensures
        i32::MIN < x + y * z < i32::MAX
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
    /* code modified by LLM (iteration 5): fixed array indexing to use proper exec indexing */
    let mut sum: i32 = 0;
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            a.len() == b.len(),
            sum == dot_product_recursive(a@, b@, 0) - dot_product_recursive(a@, b@, idx as nat),
            sum >= i32::MIN / 2,
            sum <= i32::MAX / 2,
            forall|j: int| 0 <= j < a.len() ==> a[j] >= i32::MIN / 2 && a[j] <= i32::MAX / 2,
            forall|j: int| 0 <= j < b.len() ==> b[j] >= i32::MIN / 2 && b[j] <= i32::MAX / 2,
        decreases a.len() - idx
    {
        let old_sum = sum;
        let old_idx = idx;
        
        proof {
            bounded_mul_add(sum, a[old_idx], b[old_idx]);
        }
        
        sum = sum + a[idx] * b[idx];
        idx = idx + 1;
        
        proof {
            if old_idx < a.len() {
                dot_product_recursive_unroll(a@, b@, old_idx as nat);
            }
        }
    }
    
    sum
}
// </vc-code>

}
fn main() {}