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
    let mut i: u32 = 0;
    let mut sum: u32 = 0;
    // invariant: i <= n && sum == spec_sum_to_n(i as nat) && (i == n || sum <= u32::MAX - (i+1))
    while i < n {
        if sum > u32::MAX - (i+1) {
            return None;
        }
        i = i + 1;
        sum = sum + i;
    }
    Some(sum)
}
// </vc-code>

fn main() {}
}