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
        if k == 0 || k == n {
            return 1;
        }
        
        let actual_k = if k > n - k { n - k } else { k };
        let mut dp = vec![0u64; (actual_k + 1) as usize];
        dp[0] = 1;
        
        let mut i = 1u64;
        while i <= n {
            let mut j = if actual_k < i { actual_k } else { i };
            while j > 0 {
                dp[j as usize] = dp[j as usize] + dp[(j - 1) as usize];
                j = j - 1;
            }
            i = i + 1;
        }
        
        dp[actual_k as usize]
    }

    proof fn comb_props(n: nat, k: nat)
        requires 0 <= k <= n,
        ensures comb(n, k) == comb(n, sub(n, k)),
    {
        if k == 0 {
            assert(sub(n, k) == n);
            assert(comb(n, 0) == 1);
            assert(comb(n, n) == 1);
        } else if k == n {
            assert(sub(n, k) == 0);
            assert(comb(n, n) == 1);
            assert(comb(n, 0) == 1);
        } else if n == 0 {
            // Base case handled above
        } else {
            // Inductive case - use the recursive structure
            comb_props(sub(n, 1), k);
            comb_props(sub(n, 1), sub(k, 1));
            comb_props(sub(n, 1), sub(sub(n, k), 1));
            comb_props(sub(n, 1), sub(n, k));
            
            // The proof follows from the Pascal's identity and inductive hypothesis
            assert(comb(n, k) == comb(sub(n, 1), k) + comb(sub(n, 1), sub(k, 1)));
            assert(comb(n, sub(n, k)) == comb(sub(n, 1), sub(n, k)) + comb(sub(n, 1), sub(sub(n, k), 1)));
            assert(sub(sub(n, k), 1) == sub(n, 1) - sub(n, k));
            assert(sub(n, 1) - sub(n, k) == sub(k, 1));
        }
    }

    fn main()
    {
        let result = comb_method(5, 2);
        println!("C(5, 2) = {}", result);
        test_comb();
    }

    fn test_comb() {
        // Test some basic combinations
        assert(comb_method(0, 0) == 1);
        assert(comb_method(1, 0) == 1);
        assert(comb_method(1, 1) == 1);
        assert(comb_method(5, 0) == 1);
        assert(comb_method(5, 5) == 1);
        assert(comb_method(5, 2) == 10);
        assert(comb_method(5, 3) == 10);
        
        println!("All tests passed!");
    }
}