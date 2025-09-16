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
proof fn spec_sum_to_n_is_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        spec_sum_to_n(i) <= spec_sum_to_n(j),
    decreases j - i
{
    if i < j {
        spec_sum_to_n_is_monotonic(i, (j - 1) as nat);
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
            sum as nat == spec_sum_to_n(i as nat),
        decreases n - i
    {
        i = i + 1;
        match sum.checked_add(i) {
            Some(new_sum) => sum = new_sum,
            None => return None,
        }
    }
    Some(sum)
}
// </vc-code>

}
fn main() {}