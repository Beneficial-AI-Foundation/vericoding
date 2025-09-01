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
// No helpers needed for this proof.
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
    let mut i: u32 = 0;
    let mut acc: u128 = 0u128;
    while i < n
        invariant i <= n;
        invariant acc == (spec_sum_to_n(i as nat) as u128);
        decreases (n - i) as nat;
    {
        acc = acc + (i as u128) + 1u128;
        i = i + 1;
    }

    if acc <= (u32::MAX as u128) {
        let s: u32 = acc as u32;
        proof {
            // acc == spec_sum_to_n(n as nat) as u128 by the loop invariant at termination
            assert(acc == spec_sum_to_n(n as nat) as u128);
            // round-trip cast: s as u128 == acc
            assert((s as u128) == acc);
            // therefore s as nat == spec_sum_to_n(n as nat)
            assert((s as nat) == spec_sum_to_n(n as nat));
        }
        Some(s)
    } else {
        None
    }
    // impl-end
}
// </vc-code>

fn main() {}
}