// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prefix sum and lemma relating prefix and recursive dot product */
spec fn dot_product_prefix(a: Seq<i32>, b: Seq<i32>, i: nat) -> int {
    if i == 0 {
        0
    } else {
        dot_product_prefix(a, b, i - 1) + a[(i - 1) as int] * b[(i - 1) as int]
    }
}

proof fn dot_prefix_recursive_relation(a: Seq<i32>, b: Seq<i32>, i: nat)
    requires i <= a.len()
    ensures dot_product(a, b) == dot_product_recursive(a, b, i) + dot_product_prefix(a, b, i)
    decreases i
{
    if i == 0 {
        assert(dot_product_prefix(a, b, 0) == 0);
        assert(dot_product_recursive(a, b, 0) == dot_product(a, b));
    } else {
        dot_prefix_recursive_relation(a, b, i - 1);
        assert(dot_product_recursive(a, b, i - 1) == a[(i - 1) as int] * b[(i - 1) as int] + dot_product_recursive(a, b, i));
        assert(dot_product_prefix(a, b, i) == dot_product_prefix(a, b, i - 1) + a[(i - 1) as int] * b[(i - 1) as int]);
        assert(dot_product(a, b) == dot_product_recursive(a, b, i - 1) + dot_product_prefix(a, b, i - 1));
        assert(dot_product(a, b) == dot_product_recursive(a, b, i) + dot_product_prefix(a, b, i));
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
    /* code modified by LLM (iteration 5): compute dot product iteratively with invariants */
    let mut sum: i32 = 0;
    let n: usize = a.len();
    let mut i: usize = 0;
    while i < n
        invariant i <= n;
        invariant sum == dot_product_prefix(a@, b@, i as nat);
        decreases n - i
    {
        let ai: i32 = a@[i as nat];
        let bi: i32 = b@[i as nat];
        sum = sum + ai * bi;
        i = i + 1;
    }
    proof {
        dot_prefix_recursive_relation(a@, b@, n as nat);
        assert(dot_product_recursive(a@, b@, n as nat) == 0);
        assert(sum == dot_product_prefix(a@, b@, n as nat));
        assert(sum == dot_product(a@, b@));
    }
    sum
}
// </vc-code>

}
fn main() {}