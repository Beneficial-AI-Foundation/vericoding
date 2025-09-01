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
if n == 0 {
    Some(0)
} else {
    let mut sum: u32 = 0;
    let mut i: u32 = 1;
    while i <= n
        invariant
            i >= 1 && i <= n + 1,
            sum == spec_sum_to_n((i - 1) as nat),
    {
        if let Some(new_sum) = sum.checked_add(i) {
            sum = new_sum;
        } else {
            return None;
        }
        i = i + 1;
    }
    Some(sum)
}
}
// </vc-code>

fn main() {}
}