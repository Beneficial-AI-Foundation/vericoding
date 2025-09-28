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
// Lemma to help with the recursive structure of comb
proof fn lemma_comb_base_cases(n: nat, k: nat)
    requires 0 <= k <= n
    ensures k == 0 ==> comb(n, k) == 1,
    ensures k == n ==> comb(n, k) == 1,
{
    // Base cases follow directly from the definition of comb
}

// Lemma for the recursive case
proof fn lemma_comb_recursive(n: nat, k: nat)
    requires 0 <= k <= n && n >= 1 && k >= 1 && k < n
    ensures comb(n, k) == comb((n - 1) as nat, k) + comb((n - 1) as nat, (k - 1) as nat)
{
    // Recursive case follows directly from the definition of comb
}
// </vc-helpers>

// <vc-spec>
fn Comb(n: u64, k: u64) -> (res: u64)
    requires 0 <= k <= n
    ensures res == comb(n as nat, k as nat)
// </vc-spec>
// <vc-code>
{
    if k == 0 || k == n {
        proof {
            lemma_comb_base_cases(n as nat, k as nat);
        }
        1
    } else {
        let left = Comb(n - 1, k);
        let right = Comb(n - 1, k - 1);
        proof {
            lemma_comb_recursive(n as nat, k as nat);
        }
        left + right
    }
}
// </vc-code>

fn main() {}

}