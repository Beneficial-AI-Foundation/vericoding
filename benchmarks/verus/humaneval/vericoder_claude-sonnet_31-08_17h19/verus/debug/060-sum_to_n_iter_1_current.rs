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
lemma lemma_sum_to_n_formula(n: nat)
    ensures spec_sum_to_n(n) == n * (n + 1) / 2
    decreases n
{
    if n == 0 {
        assert(spec_sum_to_n(0) == 0);
        assert(0 * (0 + 1) / 2 == 0);
    } else {
        lemma_sum_to_n_formula((n - 1) as nat);
        assert(spec_sum_to_n(n) == n + spec_sum_to_n((n - 1) as nat));
        assert(spec_sum_to_n((n - 1) as nat) == (n - 1) * n / 2);
        assert(spec_sum_to_n(n) == n + (n - 1) * n / 2);
        assert(n + (n - 1) * n / 2 == n * (n + 1) / 2);
    }
}

lemma lemma_sum_overflow_bound(n: u32)
    ensures n <= 65535 ==> spec_sum_to_n(n as nat) <= 0xFFFFFFFF
{
    if n <= 65535 {
        lemma_sum_to_n_formula(n as nat);
        assert(spec_sum_to_n(n as nat) == (n as nat) * ((n as nat) + 1) / 2);
        assert((n as nat) * ((n as nat) + 1) <= 65535 * 65536);
        assert(65535 * 65536 == 4294836480);
        assert(4294836480 / 2 == 2147418240);
        assert(2147418240 <= 0xFFFFFFFF);
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
    if n > 65535 {
        return None;
    }
    
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            i <= n,
            sum == spec_sum_to_n(i as nat),
            n <= 65535,
    {
        if sum > u32::MAX - (i + 1) {
            return None;
        }
        i = i + 1;
        sum = sum + i;
        
        assert(spec_sum_to_n(i as nat) == (i as nat) + spec_sum_to_n((i - 1) as nat));
    }
    
    proof {
        lemma_sum_overflow_bound(n);
    }
    
    Some(sum)
}
// </vc-code>

fn main() {}
}