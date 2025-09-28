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
use std::vec::Vec;
macro_rules! array2d {
    ($rows:expr, $cols:expr, $val:expr) => {{
        let mut row_vec = Vec::new();
        let mut i = 0;
        while i < $rows {
            row_vec.push(Vec::new());
            let mut j = 0;
            while j < $cols {
                row_vec.borrow_mut().index_mut(i).push($val);
                j += 1;
            }
            i += 1;
        }
        row_vec
    }};
}
// </vc-helpers>

// <vc-spec>
fn Comb(n: u64, k: u64) -> (res: u64)
    requires 0 <= k <= n
    ensures res == comb(n as nat, k as nat)
// </vc-spec>
// <vc-code>
{
    // These need to be ghost, as nat is a ghost type
    // We don't really need them to be in the code, so let's make them ghost
    let ghost n_u: nat = n as nat;
    let ghost k_u: nat = k as nat;

    if k == 0 || k == n {
        return 1;
    }
    if k > n {
        return 0; // Should not happen due to precondition, but for safety in type `u64` and `nat` conversion
    }

    let mut dp = array2d![ (n + 1) as usize, (k + 1) as usize, 0u64];

    // Initialize base cases
    // C(i, 0) = 1 for all i
    let mut i: u64 = 0;
    while i <= n
        invariant
            0 <= i <= n + 1,
            // For all i_iter < i, dp[i_iter][0] == 1
            forall |i_iter: int| 0 <= i_iter < i as int ==> dp@.index(i_iter as nat)@[0] == 1,
            dp.len() == (n + 1) as nat,
            forall |row_idx: int| #[trigger] dp@.index(row_idx as nat).len() == (k + 1) as nat,
    {
        proof {
            dp.index_mut(i as nat).set(0, 1u64);
        }
        i += 1;
    }

    // C(i, i) = 1 for all i
    let mut i: u64 = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            // For all i_iter from 1 to i-1, dp[i_iter][i_iter] == 1
            forall |i_iter: int| 1 <= i_iter < i as int ==> dp@.index(i_iter as nat)@[i_iter as nat] == 1,
            // C(m, 0) properties are preserved
            forall |m: int| 0 <= m <= n as int ==> dp@.index(m as nat)@[0] == 1,
            dp.len() == (n + 1) as nat,
            forall |row_idx: int| #[trigger] dp@.index(row_idx as nat).len() == (k + 1) as nat,
    {
        if i <= k { // Only update if i is within bounds for k columns
            proof {
                dp.index_mut(i as nat).set(i as nat, 1u64);
            }
        } else {
            // Because k is fixed, if i > k, dp[i][i] is out of bounds for the column,
            // but the principle C(i,i)=1 holds.
            // We only need to compute up to k.
        }
        i += 1;
    }

    // Fill the DP table
    let mut i: u64 = 2;
    while i <= n
        invariant
            2 <= i <= n + 1,
            // For all prev_n < i, prev_k <= prev_n:
            // if prev_k == 0 || prev_k == prev_n, dp[prev_n][prev_k] == 1
            forall |prev_n: int, prev_k: int| #[trigger]
                0 <= prev_n < i as int && 0 <= prev_k <= prev_n && prev_k <= k as int
                ==> ( (prev_k == 0 || prev_k == prev_n) ==> dp@.index(prev_n as nat)@[prev_k as nat] == 1 ),
            // For all prev_n < i, prev_k <= min(prev_n, k_u), if not base case, dp[prev_n][prev_k] == comb(prev_n, prev_k)
            forall |prev_n: int, prev_k: int| #[trigger]
                2 <= prev_n < i as int && 1 <= prev_k < prev_n && prev_k <= k as int
                ==> dp@.index(prev_n as nat)@[prev_k as nat] == comb(prev_n as nat, prev_k as nat),
            dp.len() == (n + 1) as nat,
            forall |row_idx: int| #[trigger] dp@.index(row_idx as nat).len() == (k + 1) as nat,
    {
        let mut j: u64 = 1;

        while j < i && j <= k
            invariant
                1 <= j <= i && j <= k + 1,
                // Inner invariant: for the current row i, columns from 1 to j-1 are correct
                forall |prev_k: int| #[trigger]
                    1 <= prev_k && prev_k < j as int && prev_k < i as int
                    ==> dp@.index(i as nat)@[prev_k as nat] == comb(i as nat, prev_k as nat),
                // Outer loop invariant for rows before i is preserved
                forall |prev_n: int, prev_k_out: int| #[trigger]
                    0 <= prev_n && prev_n < i as int && 0 <= prev_k_out && prev_k_out <= prev_n && prev_k_out <= k as int
                    ==> ( (prev_k_out == 0 || prev_k_out == prev_n) ==> dp@.index(prev_n as nat)@[prev_k_out as nat] == 1 ),
                forall |prev_n: int, prev_k_out: int| #[trigger]
                    2 <= prev_n && prev_n < i as int && 1 <= prev_k_out && prev_k_out < prev_n && prev_k_out <= k as int
                    ==> dp@.index(prev_n as nat)@[prev_k_out as nat] == comb(prev_n as nat, prev_k_out as nat),
                dp.len() == (n + 1) as nat,
                forall |row_idx: int| #[trigger] dp@.index(row_idx as nat).len() == (k + 1) as nat,
        {
            // C(i, j) = C(i-1, j) + C(i-1, j-1)
            let prev_n_val = dp@.index((i - 1) as nat);
            let val = prev_n_val.index(j as nat) + prev_n_val.index((j - 1) as nat);
            proof {
                dp.index_mut(i as nat).set(j as nat, val);
            }

            proof {
                assert(comb(i as nat, j as nat) == comb((i - 1) as nat, j as nat) + comb((i - 1) as nat, (j - 1) as nat));
                assert(dp@.index((i - 1) as nat)@[j as nat] == comb((i - 1) as nat, j as nat));
                assert(dp@.index((i - 1) as nat)@[(j - 1) as nat] == comb((i - 1) as nat, (j - 1) as nat));
                assert(dp@.index(i as nat)@[j as nat] == comb(i as nat, j as nat));
            }

            j += 1;
        }
        i += 1;
    }

    // Final result
    let final_res = dp@.index(n_u)@.index(k_u);

    proof {
        assert(final_res == comb(n_u, k_u));
    }

    final_res
}
// </vc-code>

fn main() {}

}