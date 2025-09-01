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
proof fn lemma_spec_succ(n: nat)
    ensures spec_sum_to_n(n + 1) == (n + 1) + spec_sum_to_n(n)
{
    // by unfolding the specification of spec_sum_to_n
    assert(spec_sum_to_n(n + 1) == (n + 1) + spec_sum_to_n(n));
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
    let mut i: u32 = 0u32;
    let mut acc: u128 = 0u128;
    while i < n
        invariant i <= n
        invariant acc == (spec_sum_to_n(i as nat) as u128)
        decreases (n - i) as nat
    {
        // maintain invariant: acc_new = spec_sum_to_n((i+1)) as u128
        proof {
            lemma_spec_succ(i as nat);
            // spec_sum_to_n((i+1)) == (i+1) + spec_sum_to_n(i)
            assert(spec_sum_to_n((i + 1) as nat) == ((i + 1) as nat) + spec_sum_to_n(i as nat));
            // cast both sides to u128 and use the invariant acc == spec_sum_to_n(i) as u128
            assert((spec_sum_to_n((i + 1) as nat) as u128) == ((i as u128) + 1u128) + (spec_sum_to_n(i as nat) as u128));
            assert((spec_sum_to_n((i + 1) as nat) as u128) == ((i as u128) + 1u128) + acc);
        }
        acc = acc + (i as u128) + 1u128;
        i = i + 1;
    }

    if acc <= (u32::MAX as u128) {
        let s: u32 = acc as u32;
        proof {
            // acc == spec_sum_to_n(n) as u128 from loop invariant at termination
            assert(acc == (spec_sum_to_n(n as nat) as u128));
            // round-trip cast: s as u128 == acc
            assert((s as u128) == acc);
            // combine to get s as u128 == spec_sum_to_n(n) as u128
            assert((s as u128) == (spec_sum_to_n(n as nat) as u128));
            // cast to nat and compare (both are within u32 range)
            assert(((s as nat) as u128) == (spec_sum_to_n(n as nat) as u128));
            assert((s as nat) == spec_sum_to_n(n as nat));
        }
        Some(s)
    } else {
        None
    }
}
// </vc-code>

fn main() {}
}