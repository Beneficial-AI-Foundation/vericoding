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
    ensures 2 * spec_sum_to_n(n) == n * (n + 1)
    decreases n
{
    if n == 0 {
        assert(spec_sum_to_n(0) == 0);
        assert(2 * spec_sum_to_n(0) == 0);
    } else {
        let k: nat = (n - 1) as nat;
        lemma_sum_formula(k);
        // spec_sum_to_n(n) = n + spec_sum_to_n(k)
        assert(spec_sum_to_n(n) == n + spec_sum_to_n(k));
        // multiply both sides by 2
        assert(2 * spec_sum_to_n(n) == 2 * (n + spec_sum_to_n(k)));
        assert(2 * (n + spec_sum_to_n(k)) == 2 * n + 2 * spec_sum_to_n(k));
        // from IH: 2 * spec_sum_to_n(k) == k * (k + 1)
        assert(2 * spec_sum_to_n(k) == k * (k + 1));
        assert(2 * n + 2 * spec_sum_to_n(k) == 2 * n + k * (k + 1));
        // n = k + 1
        assert(n == k + 1);
        // algebra: 2*n + k*(k+1) == n*(n+1)
        // k*(k+1) = (n-1)*n = n*n - n, so 2*n + (n*n - n) = n*n + n = n*(n+1)
        assert(2 * n + k * (k + 1) == n * (n + 1));
        assert(2 * spec_sum_to_n(n) == n * (n + 1));
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
    let nn: u128 = n as u128;
    // prove bounds to avoid overflow concerns in later u128 arithmetic
    proof {
        // nn originates from a u32, so it's at most u32::MAX
        assert(nn <= (u32::MAX as u128));
        // hence nn*(nn+1) is at most u32::MAX*(u32::MAX+1) < u128::MAX
        assert(nn * (nn + 1) <= (u32::MAX as u128) * ((u32::MAX as u128) + 1));
        assert((u32::MAX as u128) * ((u32::MAX as u128) + 1) < (u128::MAX));
        assert(nn * (nn + 1) <= u128::MAX);
    }

    let s128: u128;
    if nn % 2 == 0 {
        s128 = (nn / 2) * (nn + 1);
    } else {
        s128 = ((nn + 1) / 2) * nn;
    }
    if (s128 <= (u32::MAX as u128)) {
        let s_u32: u32 = s128 as u32;
        proof {
            // relate spec to arithmetic formula (proved in lemma)
            lemma_sum_formula(n as nat);
            let spec_u128: u128 = spec_sum_to_n(n as nat) as u128;
            // from lemma: 2 * spec_sum_to_n(n) == n*(n+1)
            assert(2 * spec_u128 == nn * (nn + 1));
            // show 2 * s128 == nn*(nn+1) by cases based on how s128 was computed
            if nn % 2 == 0 {
                assert(s128 == (nn / 2) * (nn + 1));
                assert(2 * s128 == 2 * ((nn / 2) * (nn + 1)));
                // (2 * (nn/2)) * (nn+1) == nn * (nn+1)
                assert(2 * ((nn / 2) * (nn + 1)) == nn * (nn + 1));
            } else {
                assert(s128 == ((nn + 1) / 2) * nn);
                assert(2 * s128 == 2 * (((nn + 1) / 2) * nn));
                // 2 * ((nn+1)/2) * nn == (nn+1) * nn == nn*(nn+1)
                assert(2 * (((nn + 1) / 2) * nn) == nn * (nn + 1));
            }
            assert(2 * s128 == nn * (nn + 1));
            // from 2*spec_u128 == nn*(nn+1) and 2*s128 == nn*(nn+1) deduce spec_u128 == s128
            assert(spec_u128 == s128);
            // relate back to the spec's nat result: cast s_u32 to nat and compare
            assert(spec_sum_to_n(n as nat) == s_u32 as nat);
        }
        Some(s_u32)
    } else {
        None
    }
}
// </vc-code>

fn main() {}
}