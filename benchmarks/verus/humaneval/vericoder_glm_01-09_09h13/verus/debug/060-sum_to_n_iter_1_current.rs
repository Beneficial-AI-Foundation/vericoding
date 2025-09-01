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
proof fn lemma_sum_to_n_is_recursive(n: nat)
    decreases n
{
    if n > 0 {
        lemma_sum_to_n_is_recursive((n - 1) as nat);
        assert(spec_sum_to_n(n) == n + spec_sum_to_n((n - 1) as nat));
    }
}

proof fn lemma_sum_to_n_nonnegative(n: nat)
    decreases n
{
    if n == 0 {
        assert(spec_sum_to_n(0) == 0);
    } else {
        lemma_sum_to_n_nonnegative((n - 1) as nat);
        assert(spec_sum_to_n(n) == n + spec_sum_to_n((n - 1) as nat));
        assert(spec_sum_to_n((n - 1) as nat) >= 0);
        assert(n + spec_sum_to_n((n - 1) as nat) >= 0);
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
    // impl-start
    proof {
        lemma_sum_to_n_nonnegative(n as nat);
    }
    if n == 0 {
        Some(0)
    } else {
        let prev = sum_to_n(n - 1);
        match prev {
            None => None,
            Some(prev_val) => {
                let new_sum = prev_val + n;
                proof {
                    lemma_sum_to_n_is_recursive((n - 1) as nat);
                    assert(spec_sum_to_n(n as nat) == n + spec_sum_to_n((n - 1) as nat));
                    assert(prev_val == spec_sum_to_n((n - 1) as nat));
                    assert(new_sum == spec_sum_to_n(n as nat));
                }
                if new_sum >= prev_val {
                    Some(new_sum)
                } else {
                    None
                }
            }
        }
    }
    // impl-end
}
// </vc-code>

fn main() {}
}