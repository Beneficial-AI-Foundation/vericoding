// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_unfold_dot_product_recursive_in_range(a: Seq<i32>, b: Seq<i32>, i: nat)
    requires
        a.len() == b.len(),
        i < a.len(),
    ensures
        dot_product_recursive(a, b, i) == a[i as int] * b[i as int] + dot_product_recursive(a, b, i + 1),
{
    assert(dot_product_recursive(a, b, i) == a[i as int] * b[i as int] + dot_product_recursive(a, b, i + 1));
}

proof fn lemma_dot_product_recursive_at_len_is_zero(a: Seq<i32>, b: Seq<i32>)
    requires
        a.len() == b.len(),
    ensures
        dot_product_recursive(a, b, a.len()) == 0,
{
    assert(dot_product_recursive(a, b, a.len()) == 0);
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
    let n = a.len();
    let mut i: usize = 0;
    let mut acc: i32 = 0;
    while i < n
        invariant
            a.len() == b.len(),
            n == a.len(),
            i <= n,
            (acc as int) + dot_product_recursive(a@, b@, i as nat) == dot_product(a@, b@),
        decreases n - i
    {
        proof {
            assert(i < a.len());
            lemma_unfold_dot_product_recursive_in_range(a@, b@, i as nat);
        }
        let ai = a[i];
        let bi = b[i];
        acc = acc + ai * bi;
        i = i + 1;
    }
    proof {
        assert(i == n);
        lemma_dot_product_recursive_at_len_is_zero(a@, b@);
    }
    acc
}
// </vc-code>

}
fn main() {}