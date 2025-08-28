use vstd::prelude::*;

verus! {

/* 
 * Formal specification and verification of a dynamic programming algorithm for calculating C(n, k).
 * FEUP, MIEIC, MFES, 2020/21.
 */

// Initial recursive definition of C(n, k), based on the Pascal equality.
spec fn comb(n: nat, k: nat) -> nat
    recommends 0 <= k <= n
    decreases n
    when n >= 1 && k >= 1
{
    if k == 0 || k == n { 
        1 
    } else { 
        comb((n - 1) as nat, k) + comb((n - 1) as nat, (k - 1) as nat)
    }
}

// <vc-helpers>
proof fn comb_base_cases(n: nat, k: nat)
    requires 0 <= k <= n
    ensures k == 0 ==> comb(n, k) == 1
    ensures k == n ==> comb(n, k) == 1
{
}

proof fn comb_pascal_property(n: nat, k: nat)
    requires 0 < k < n
    ensures comb(n, k) == comb((n - 1) as nat, k) + comb((n - 1) as nat, (k - 1) as nat)
{
}

proof fn comb_monotonic_bound(n: nat, k: nat)
    requires 0 <= k <= n
    ensures comb(n, k) >= 1
    decreases n
{
    if k == 0 || k == n {
    } else {
        comb_monotonic_bound((n - 1) as nat, k);
        comb_monotonic_bound((n - 1) as nat, (k - 1) as nat);
    }
}

proof fn comb_fits_u64(n: nat, k: nat)
    requires 0 <= k <= n <= 64
    ensures comb(n, k) <= 0xFFFFFFFFFFFFFFFF
    decreases n
{
    if k == 0 || k == n {
        assert(comb(n, k) == 1);
    } else if n >= 1 && k >= 1 {
        comb_fits_u64((n - 1) as nat, k);
        comb_fits_u64((n - 1) as nat, (k - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn Comb(n: u64, k: u64) -> (res: u64)
    requires 0 <= k <= n
    ensures res == comb(n as nat, k as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    proof {
        comb_fits_u64(n as nat, k as nat);
    }
    
    if k == 0 || k == n {
        1
    } else {
        let left = Comb(n - 1, k);
        let right = Comb(n - 1, k - 1);
        left + right
    }
}
// </vc-code>

fn main() {}

}