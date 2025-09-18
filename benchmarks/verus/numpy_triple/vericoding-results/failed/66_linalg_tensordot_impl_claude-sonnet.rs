// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type errors by using sequence indexing */
proof fn dot_product_lemma(a: Seq<i32>, b: Seq<i32>, i: nat, sum: i32)
    requires
        i <= a.len(),
        a.len() == b.len(),
        sum == dot_product_recursive(a, b, 0) - dot_product_recursive(a, b, i)
    ensures
        i < a.len() ==> sum + a[i as int] * b[i as int] == dot_product_recursive(a, b, 0) - dot_product_recursive(a, b, (i + 1) as nat)
{
    if i < a.len() {
        assert(dot_product_recursive(a, b, i) == a[i as int] * b[i as int] + dot_product_recursive(a, b, (i + 1) as nat));
    }
}

proof fn bounds_lemma(a: Vec<i32>, b: Vec<i32>, i: usize)
    requires
        a.len() == b.len(),
        i < a.len()
    ensures
        i < b.len()
{
}

proof fn overflow_safe_lemma(a: Seq<i32>, b: Seq<i32>, i: nat, sum: i32)
    requires
        i < a.len(),
        a.len() == b.len(),
        a.len() <= 1000,
        forall|j: nat| j < a.len() ==> -1000 <= a[j as int] <= 1000,
        forall|j: nat| j < b.len() ==> -1000 <= b[j as int] <= 1000,
        -1000000000 <= sum <= 1000000000
    ensures
        -2147483648 <= sum + a[i as int] * b[i as int] <= 2147483647
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
    /* code modified by LLM (iteration 5): simplified to use basic dot product calculation */
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            sum == dot_product_recursive(a@, b@, 0) - dot_product_recursive(a@, b@, i as nat)
        decreases a.len() - i
    {
        proof {
            bounds_lemma(a, b, i);
            dot_product_lemma(a@, b@, i as nat, sum);
        }
        sum = sum + a[i] * b[i];
        i = i + 1;
    }
    sum
}
// </vc-code>

}
fn main() {}