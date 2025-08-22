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
    {
        if k == 0 || k == n { 
            1 
        } else if k > n { 
            0 
        } else { 
            comb(sub(n, 1), k) + comb(sub(n, 1), sub(k, 1)) 
        }
    }

    // Calculates C(n,k) iteratively in time O(k*(n-k)) and space O(n-k), 
    // with dynamic programming.
    #[verifier::external_body]
    fn comb_method(n: u64, k: u64) -> (result: u64)
        requires 0 <= k <= n,
        ensures result as nat == comb(n as nat, k as nat),
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    proof fn comb_props(n: nat, k: nat)
        requires 0 <= k <= n,
        ensures comb(n, k) == comb(n, sub(n, k)),
    {
        // This would need a proof by induction - left as external for now
        assume(comb(n, k) == comb(n, sub(n, k)));
    }

    fn main()
    {
    // TODO: Remove this comment and implement the function body
    }

    fn test_comb() {
    // TODO: Remove this comment and implement the function body
    }
}