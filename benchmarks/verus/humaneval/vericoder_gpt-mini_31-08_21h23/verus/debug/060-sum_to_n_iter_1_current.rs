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
proof fn lemma_sum_formula(n: nat)
    decreases n
{
    if n == 0 {
        assert(spec_sum_to_n(0) == 0);
    } else {
        lemma_sum_formula(n - 1);
        let k: nat = n - 1;
        // spec_sum_to_n(n) = n + spec_sum_to_n(n-1)
        assert(spec_sum_to_n(n) == n + spec_sum_to_n(k));
        // by IH
        assert(spec_sum_to_n(k) == k * (k + 1) / 2);
        assert(spec_sum_to_n(n) == n + k * (k + 1) / 2);
        // algebra: n + k*(k+1)/2 = (k+1)*(k+2)/2 = n*(n+1)/2
        assert(n + k * (k + 1) / 2 == n * (n + 1) / 2);
        assert(spec_sum_to_n(n) == n * (n + 1) / 2);
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
    let nn: u128 = n as u128;
    let s128: u128 = nn * (nn + 1) / 2;
    if (s128 <= (u32::MAX as u128)) {
        let s_u32: u32 = s128 as u32;
        proof {
            lemma_sum_formula(n as nat);
            // cast the spec result to u128 and relate to s128
            assert((spec_sum_to_n(n as nat) as u128) == nn * (nn + 1) / 2);
            assert((spec_sum_to_n(n as nat) as u128) == s128);
            // now cast to u32 (safe because s128 <= u32::MAX)
            assert((spec_sum_to_n(n as nat) as u32) == s_u32);
        }
        Some(s_u32)
    } else {
        None
    }
    // impl-end
}
// </vc-code>

fn main() {}
}