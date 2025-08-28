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
proof fn lemma_sum_to_n(n: nat)
    ensures spec_sum_to_n(n) == (n * (n + 1)) / 2,
    decreases n,
{
    if n == 0 {
        assert(spec_sum_to_n(0) == 0);
        assert((0 * (0 + 1)) / 2 == 0);
    } else {
        lemma_sum_to_n((n - 1) as nat);
        assert(spec_sum_to_n(n) == n + spec_sum_to_n((n - 1) as nat));
        assert(spec_sum_to_n((n - 1) as nat) == (((n - 1) as nat) * (n)) / 2);
        assert(spec_sum_to_n(n) == n + (((n - 1) as nat) * n) / 2);
        assert(spec_sum_to_n(n) == (2 * n + ((n - 1) as nat) * n) / 2);
        assert(spec_sum_to_n(n) == (n * (2 + (n - 1) as nat)) / 2);
        assert(spec_sum_to_n(n) == (n * (n + 1)) / 2);
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
        decreases n - i,
    {
        if sum > u32::MAX - (i + 1) {
            return None;
        }
        sum = sum + (i + 1);
        i = i + 1;
    }
    proof {
        lemma_sum_to_n(n as nat);
        assert(spec_sum_to_n(n as nat) == (n as nat * (n as nat + 1)) / 2);
    }
    Some(sum)
}
// </vc-code>

}
fn main() {}