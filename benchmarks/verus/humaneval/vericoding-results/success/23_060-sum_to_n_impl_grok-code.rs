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

// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: u32) -> (sum: Option<u32>)

    ensures
        sum.is_some() ==> sum.unwrap() == spec_sum_to_n(n as nat),
// </vc-spec>
// <vc-code>
    decreases n as nat
{
    if n == 0 {
        return Some(0);
    } else {
        if let Some(prev) = sum_to_n(n - 1) {
            return prev.checked_add(n);
        } else {
            return None;
        }
    }
}
// </vc-code>

}
fn main() {}