use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn sum_formula(i: nat) -> nat {
    i * (i + 1) / 2
}

proof fn sum_formula_step(i: nat)
    requires i >= 0
    ensures sum_formula(i) + (i + 1) == sum_formula(i + 1)
{
    assert(sum_formula(i) + (i + 1) == i * (i + 1) / 2 + (i + 1));
    assert(i * (i + 1) / 2 + (i + 1) == i * (i + 1) / 2 + 2 * (i + 1) / 2) by {
        assert(i + 1 == 2 * (i + 1) / 2);
    }
    assert(i * (i + 1) / 2 + 2 * (i + 1) / 2 == (i * (i + 1) + 2 * (i + 1)) / 2) by {
        assert(i * (i + 1) + 2 * (i + 1) == (i + 2) * (i + 1));
    }
    assert((i * (i + 1) + 2 * (i + 1)) / 2 == (i + 1) * (i + 2) / 2) by {
        assert(i * (i + 1) + 2 * (i + 1) == (i + 1) * (i + 2));
    }
    assert((i + 1) * (i + 2) / 2 == sum_formula(i + 1));
}

proof fn monotonic_formula(i: nat, j: nat)
    requires i <= j
    ensures sum_formula(i) <= sum_formula(j)
{
}
// </vc-helpers>

// <vc-spec>
fn sum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    
    assert(n * (n + 1) / 2 <= u32::MAX) by {
        assert(n <= u32::MAX);
        assert(n * (n + 1) <= 2 * u32::MAX);
    }
    
    let mut i: u32 = 0;
    let mut sum: u32 = 0;
    
    while i < n
        invariant 
            i <= n,
            sum == i * (i + 1) / 2,
            n * (n + 1) / 2 <= u32::MAX,
        decreases n - i,
    {
        proof {
            sum_formula_step(i as nat);
            assert(i < n);
            assert(i + 1 <= n);
            monotonic_formula((i + 1) as nat, n as nat);
            assert((i + 1) * (i + 2) / 2 <= n * (n + 1) / 2);
            assert((i + 1) * (i + 2) / 2 <= u32::MAX);
            assert(sum + (i + 1) <= u32::MAX);
        }
        i = i + 1;
        sum = sum + i;
        assert(sum == i * (i + 1) / 2);
    }
    
    sum
}
// </vc-code>

fn main() {}

}