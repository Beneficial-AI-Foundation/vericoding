use vstd::prelude::*;

verus! {

spec fn spec_sum_to_n(n: nat) -> (ret:nat)
    decreases n,
{
    if (n == 0) {
        0
    } else {
        n + spec_sum_to_n((n - 1) as nat)
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_spec_sum_to_n_nonnegative(n: nat)
    ensures
        spec_sum_to_n(n) >= 0,
    decreases n,
{
    if n > 0 {
        lemma_spec_sum_to_n_nonnegative((n - 1) as nat);
    }
}

proof fn lemma_spec_sum_to_n_monotonic(m: nat, n: nat)
    requires
        m <= n,
    ensures
        spec_sum_to_n(m) <= spec_sum_to_n(n),
    decreases n - m,
{
    if m < n {
        lemma_spec_sum_to_n_monotonic(m, (n - 1) as nat);
        assert(spec_sum_to_n(n) == n + spec_sum_to_n((n - 1) as nat));
    }
}

proof fn lemma_spec_sum_to_n_formula(n: nat)
    ensures
        spec_sum_to_n(n) == n * (n + 1) / 2,
    decreases n,
{
    if n > 0 {
        lemma_spec_sum_to_n_formula((n - 1) as nat);
        assert(spec_sum_to_n(n) == n + spec_sum_to_n((n - 1) as nat));
        assert(spec_sum_to_n((n - 1) as nat) == ((n - 1) * n) / 2);
        assert(spec_sum_to_n(n) == n + ((n - 1) * n) / 2);
        assert(spec_sum_to_n(n) == (2*n + (n - 1)*n) / 2);
        assert(spec_sum_to_n(n) == (n*(n + 1)) / 2);
    }
}

proof fn lemma_spec_sum_to_n_step(i: nat)
    requires
        i > 0,
    ensures
        spec_sum_to_n(i) == i + spec_sum_to_n((i - 1) as nat),
{
}

proof fn lemma_arithmetic_overflow_prevention(n: u32, i: u32)
    requires
        i <= n,
    ensures
        (n - i) >= 0,
{
}

proof fn lemma_sum_addition(i: nat, sum: u32)
    requires
        i as u32 <= u32::MAX,
        sum == spec_sum_to_n(i),
    ensures
        spec_sum_to_n(i) + (i + 1) as nat == spec_sum_to_n((i + 1) as nat),
{
    assert(spec_sum_to_n((i + 1) as nat) == (i + 1) as nat + spec_sum_to_n(i));
}

proof fn lemma_checked_add_safe(a: u32, b: u32)
    requires
        a <= u32::MAX - b,
    ensures
        a.checked_add(b).is_some(),
{
}

proof fn lemma_sum_to_n_bounds(n: nat)
    ensures
        spec_sum_to_n(n) <= (u32::MAX as nat),
    decreases n,
{
    if n > 0 {
        lemma_sum_to_n_bounds((n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: u32) -> (sum: Option<u32>)
    // post-conditions-start
    ensures
        sum.is_some() ==> sum.unwrap() == spec_sum_to_n(n as nat),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    
    proof {
        lemma_sum_to_n_bounds(n as nat);
    }
    
    while i <= n
        invariant
            i <= n + 1,
            sum == spec_sum_to_n(i as nat),
            spec_sum_to_n(i as nat) <= spec_sum_to_n(n as nat),
            spec_sum_to_n(i as nat) <= (u32::MAX as nat),
        decreases (n - i) as nat,
    {
        if i < n {
            proof {
                lemma_arithmetic_overflow_prevention(n, i);
                lemma_sum_addition(i as nat, sum);
                assert(spec_sum_to_n((i + 1) as nat) == spec_sum_to_n(i as nat) + (i + 1) as nat);
                assert(spec_sum_to_n(i as nat) <= u32::MAX as nat - (i + 1));
                lemma_checked_add_safe(sum, i + 1);
                lemma_checked_add_safe(i, 1);
            }
            let new_i = i.checked_add(1).unwrap();
            let new_sum = sum.checked_add(new_i).unwrap();
            proof {
                assert(new_i as nat == (i as nat) + 1);
                assert(new_sum as nat == sum as nat + new_i as nat);
                assert(sum as nat == spec_sum_to_n(i as nat));
                assert(new_sum as nat == spec_sum_to_n(i as nat) + (i + 1) as nat);
                assert(new_sum as nat == spec_sum_to_n((i + 1) as nat));
            }
            i = new_i;
            sum = new_sum;
        } else {
            proof {
                lemma_checked_add_safe(i, 1);
            }
            let new_i = i.checked_add(1).unwrap();
            i = new_i;
        }
    }
    
    Some(sum)
}
// </vc-code>

fn main() {}
}