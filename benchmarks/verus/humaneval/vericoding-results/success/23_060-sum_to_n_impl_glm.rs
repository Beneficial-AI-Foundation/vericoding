// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
proof fn lemma_spec_sum_to_n_recursive(n: nat)
    ensures
        n > 0 ==> spec_sum_to_n(n) == n + spec_sum_to_n((n-1) as nat)
{
    if n > 0 {
        assert(spec_sum_to_n(n) == n + spec_sum_to_n((n-1) as nat));
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: u32) -> (sum: Option<u32>)

    ensures
        sum.is_some() ==> sum.unwrap() == spec_sum_to_n(n as nat),
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = 0;
    let mut sum: u32 = 0;

    while i < n
        invariant
            i <= n,
            sum == spec_sum_to_n(i as nat),
        decreases n - i
    {
        let next = i + 1;
        if sum > u32::MAX - next {
            return None;
        }
        sum = sum + next;
        i = next;

        proof {
            lemma_spec_sum_to_n_recursive(i as nat);
        }
    }

    Some(sum)
}
// </vc-code>

}
fn main() {}