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
proof { decreases n; }

if n == 0 {
    Some(0)
} else {
    let prev_option = sum_to_n(n - 1);
    match prev_option {
        Some(prev) => {
            if let Some(new_sum) = prev.checked_add(n) {
                Some(new_sum)
            } else {
                None
            }
        }
        None => None
    }
}
}
// </vc-code>

fn main() {}
}