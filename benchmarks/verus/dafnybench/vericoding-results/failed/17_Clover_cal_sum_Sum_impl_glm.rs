use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::calc;

fn lemma_sum_property(n: u32)
    requires
        n >= 0,
    ensures
        n * (n + 1) / 2 == if n == 0 { 0 } else { (n - 1) * n / 2 + n }
{
    if n > 0 {
        calc! {
            (n * (n + 1)) / 2;
            == { (n * (n + 1)) == n * n + n }
            (n * n + n) / 2;
            == { (n * n + n) == (n * n - n) + 2 * n }
            ((n * n - n) + 2 * n) / 2;
            == { assert((n - 1) * n == n * n - n); }
            ((n - 1) * n + 2 * n) / 2;
            == { assert(((n - 1) * n + 2 * n) / 2 == (n - 1) * n / 2 + n); }
            (n - 1) * n / 2 + n;
        }
    }
}

proof fn lemma_inductive_sum(n: u32)
    requires
        n >= 0,
    ensures
        n * (n + 1) / 2 == n + (if n == 0 { 0 } else { (n - 1) * n / 2 })
{
    lemma_sum_property(n);
}
// </vc-helpers>

// <vc-spec>
fn sum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
{
    let mut s: u32 = 0;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            s == i * (i + 1) / 2
    {
        s = s + i;
        i = i + 1;
        lemma_inductive_sum(i);
        assert(s == (i - 1) * i / 2 + i);
    }
    
    proof {
        lemma_sum_property(n);
    }
    s
}
// </vc-code>

fn main() {}

}