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
// Added lemma proving closed-form of spec_sum_to_n to aid verification.
proof fn lemma_sum_formula(n: nat)
    ensures spec_sum_to_n(n) == n * (n + 1) / 2
    decreases n
{
    if n == 0 {
        assert(spec_sum_to_n(0) == 0);
        assert(0 == 0 * (0 + 1) / 2);
    } else {
        lemma_sum_formula((n - 1) as nat);
        // spec_sum_to_n(n) == n + spec_sum_to_n(n-1)
        assert(spec_sum_to_n(n) == n + spec_sum_to_n((n - 1) as nat));
        // by IH spec_sum_to_n(n-1) == (n-1)*n/2
        assert(spec_sum_to_n((n - 1) as nat) == (n - 1) * n / 2);
        // arithmetic: n + (n-1)*n/2 == n*(n+1)/2
        assert(n + (n - 1) * n / 2 == n * (n + 1) / 2);
        // combine to conclude
        assert(spec_sum_to_n(n) == n * (n + 1) / 2);
    }
}

// Lemma to relate nat arithmetic cast to u128 arithmetic (handles division by 2)
proof fn lemma_cast_mult_div(n: nat)
    ensures ((n * (n + 1) / 2) as u128) == (n as u128) * ((n as u128) + 1u128) / 2u128
{
    if n % 2 == 0 {
        let k = n / 2;
        // n*(n+1)/2 == k*(n+1)
        assert(n * (n + 1) / 2 == k * (n + 1));
        // cast k*(n+1) to u128 equals (k as u128)*(n+1 as u128)
        assert((k * (n + 1)) as u128 == (k as u128) * ((n + 1) as u128));
        // (n as u128)*((n as u128)+1)/2u128 == (k as u128)*((n as u128)+1u128)
        assert((n as u128) * ((n as u128) + 1u128) / 2u128 == (k as u128) * ((n as u128) + 1u128));
        // (k as u128) * ((n as u128) + 1u128) == (k as u128) * ((n + 1) as u128)
        assert((k as u128) * ((n as u128) + 1u128) == (k as u128) * ((n + 1) as u128));
        // combine
        assert((n * (n + 1) / 2) as u128 == (n as u128) * ((n as u128) + 1u128) / 2u128);
    } else {
        let k = (n + 1) / 2;
        // n*(n+1)/2 == n*k
        assert(n * (n + 1) / 2 == n * k);
        // cast n*k to u128 equals (n as u128)*(k as u128)
        assert((n * k) as u128 == (n as u128) * (k as u128));
        // (n as u128)*((n as u128)+1u128)/2u128 == (n as u128)*(k as u128)
        assert((n as u128) * ((n as u128) + 1u128) / 2u128 == (n as u128) * (k as u128));
        // combine
        assert((n * (n + 1) / 2) as u128 == (n as u128) * ((n as u128) + 1u128) / 2u128);
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
    // Compute closed-form sum = n*(n+1)/2 in u128, then check overflow for u32.
    let acc: u128 = (n as u128) * ((n as u128) + 1u128) / 2u128;
    if acc <= (u32::MAX as u128) {
        let s: u32 = acc as u32;
        proof {
            // relate computed acc with the spec via lemmas
            lemma_sum_formula(n as nat);
            lemma_cast_mult_div(n as nat);
            // spec_sum_to_n(n) == n*(n+1)/2 as nat, cast both sides to u128
            assert((spec_sum_to_n(n as nat) as u128) == ((n as nat) * ((n as nat) + 1) / 2) as u128);
            // cast equality to u128 arithmetic using lemma_cast_mult_div
            assert(((n as nat) * ((n as nat) + 1) / 2) as u128 == acc);
            assert((spec_sum_to_n(n as nat) as u128) == acc);
            // round-trip cast
            assert((s as u128) == acc);
            // conclude numeric equality at nat level
            assert((s as nat) as u128 == (spec_sum_to_n(n as nat) as u128));
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