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
proof fn lemma_sum_to_n_identity(n: nat)
    ensures
        spec_sum_to_n(n) == n * (n + 1) / 2,
    decreases n,
{
    if n == 0 {
        assert(spec_sum_to_n(0) == 0);
    } else {
        lemma_sum_to_n_identity((n - 1) as nat);
        assert(spec_sum_to_n(n) == n + spec_sum_to_n((n - 1) as nat));
        assert(spec_sum_to_n((n - 1) as nat) == (n - 1) * n / 2);
    }
}

proof fn lemma_sum_decomposition(n: nat, i: nat)
    requires i <= n,
    ensures spec_sum_to_n(n) == spec_sum_to_n(i) + (spec_sum_to_n(n) - spec_sum_to_n(i)),
{
}

proof fn lemma_sum_step(i: nat)
    ensures spec_sum_to_n(i + 1) == spec_sum_to_n(i) + (i + 1),
{
    assert(spec_sum_to_n(i + 1) == (i + 1) + spec_sum_to_n(i)) by {
        reveal(spec_sum_to_n);
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
    
    while i < n
        invariant
            i <= n,
            sum == spec_sum_to_n(i as nat),
            sum <= u32::MAX,
        decreases n - i,
    {
        if sum > u32::MAX - (i + 1) {
            return None;
        }
        
        i = i + 1;
        sum = sum + i;
        
        proof {
            lemma_sum_step((i - 1) as nat);
            assert(spec_sum_to_n(i as nat) == spec_sum_to_n((i - 1) as nat) + i);
        }
    }
    
    assert(i == n);
    assert(sum == spec_sum_to_n(n as nat));
    Some(sum)
}
// </vc-code>

fn main() {}
}