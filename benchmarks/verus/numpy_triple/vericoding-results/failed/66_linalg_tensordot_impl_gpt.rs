// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn dot_prefix(a: Seq<i32>, b: Seq<i32>, n: nat) -> int {
    dot_product_recursive(a, b, 0) - dot_product_recursive(a, b, n)
}

proof fn lemma_dot_prefix_step(a: Seq<i32>, b: Seq<i32>, n: nat)
    requires
        a.len() == b.len(),
        n < a.len()
    ensures
        dot_prefix(a, b, n + 1) == dot_prefix(a, b, n) + a[n as int] * b[n as int]
{
    let d0 = dot_product_recursive(a, b, 0);
    let dn = dot_product_recursive(a, b, n);
    let dn1 = dot_product_recursive(a, b, n + 1);
    assert(dn == a[n as int] * b[n as int] + dn1);
    assert(dot_prefix(a, b, n) == d0 - dn);
    assert(dot_prefix(a, b, n + 1) == d0 - dn1);
    assert(d0 - dn1 == d0 - (dn - a[n as int] * b[n as int]));
    assert(d0 - (dn - a[n as int] * b[n as int]) == (d0 - dn) + a[n as int] * b[n as int]);
}

proof fn lemma_dot_prefix_full(a: Seq<i32>, b: Seq<i32>)
    requires a.len() == b.len()
    ensures dot_prefix(a, b, a.len()) == dot_product(a, b)
{
    assert(dot_product_recursive(a, b, a.len()) == 0);
    assert(dot_prefix(a, b, a.len()) == dot_product_recursive(a, b, 0) - dot_product_recursive(a, b, a.len()));
    assert(dot_product(a, b) == dot_product_recursive(a, b, 0));
    assert(dot_prefix(a, b, a.len()) == dot_product(a, b));
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
            a.len() == n,
            b.len() == n,
            a@.len() == n,
            b@.len() == n,
            i <= n,
            acc as int == dot_prefix(a@, b@, i as nat)
        decreases n - i
    {
        proof {
            lemma_dot_prefix_step(a@, b@, i as nat);
        }
        acc = acc + a[i] * b[i];
        i = i + 1;
    }
    proof {
        lemma_dot_prefix_full(a@, b@);
        assert(i == n);
        assert(acc as int == dot_prefix(a@, b@, n as nat));
        assert(acc as int == dot_product(a@, b@));
    }
    acc
}
// </vc-code>

}
fn main() {}