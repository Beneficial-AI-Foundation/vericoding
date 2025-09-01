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
proof fn lemma_sum_to_n_loop(n: nat, i: nat, sum: nat)
    requires
        i <= n,
        sum == spec_sum_to_n(i),
    ensures
        sum + spec_sum_to_n((n - i) as nat) == spec_sum_to_n(n),
    decreases n - i,
{
    if i == n {
        assert(n - i == 0);
        assert(spec_sum_to_n(0) == 0);
        assert(sum + 0 == sum);
        assert(sum == spec_sum_to_n(n));
    } else {
        assert(i < n);
        assert(spec_sum_to_n((n - i) as nat) == (n - i) + spec_sum_to_n((n - i - 1) as nat)) by {
            reveal(spec_sum_to_n);
        }
        assert(sum + (n - i) == spec_sum_to_n(i) + (n - i));
        assert(spec_sum_to_n(i + 1) == (i + 1) + spec_sum_to_n(i)) by {
            reveal(spec_sum_to_n);
        }
        assert(spec_sum_to_n(i + 1) == spec_sum_to_n(i) + (i + 1));
        lemma_sum_to_n_loop(n, i + 1, sum + (i + 1));
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
    {
        if sum > u32::MAX - (i + 1) {
            return None;
        }
        
        i = i + 1;
        sum = sum + i;
        
        assert(spec_sum_to_n(i as nat) == (i as nat) + spec_sum_to_n((i - 1) as nat)) by {
            reveal(spec_sum_to_n);
        }
    }
    
    assert(i == n);
    assert(sum == spec_sum_to_n(n as nat));
    Some(sum)
}
// </vc-code>

fn main() {}
}