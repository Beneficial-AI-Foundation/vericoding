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
// Helper lemma: C(n, 0) = 1 for all n
proof fn comb_n_0(n: nat)
    ensures comb(n, 0) == 1
{
    // Base case follows directly from definition
}

// Helper lemma: C(n, n) = 1 for all n
proof fn comb_n_n(n: nat)
    ensures comb(n, n) == 1
{
    // Base case follows directly from definition
}

// Helper lemma for Pascal's identity
proof fn pascal_identity(n: nat, k: nat)
    requires 0 < k < n
    ensures comb(n, k) == comb((n - 1) as nat, k) + comb((n - 1) as nat, (k - 1) as nat)
    decreases n
{
    // Follows directly from the recursive definition
}

// Helper lemma: C(0, j) = 0 for j > 0
proof fn comb_0_j(j: nat)
    requires j > 0
    ensures comb(0, j) == 0
{
    // By definition, k > n means C(n,k) = 0
}

// Invariant helper: the dp array at row i contains C(i, j) for all valid j
spec fn row_invariant(dp: Seq<u64>, row: nat, max_k: nat) -> bool {
    dp.len() == (max_k + 1) as nat &&
    forall|j: nat| #[trigger] (j <= row && j <= max_k) ==> dp[j as int] == comb(row, j)
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
        return 1;
    }
    
    // Create dp array to store one row at a time
    let mut dp: Vec<u64> = Vec::new();
    
    // Initialize first row (row 0): C(0, 0) = 1, C(0, j) = 0 for j > 0
    let mut i: usize = 0;
    while i <= k as usize
        invariant
            i <= k as usize + 1,
            dp.len() == i,
            forall|j: nat| j < i as nat ==> #[trigger] dp@[j as int] == comb(0, j)
    {
        if i == 0 {
            dp.push(1);
            proof {
                assert(comb(0, 0) == 1);
            }
        } else {
            dp.push(0);
            proof {
                comb_0_j(i as nat);
                assert(comb(0, i as nat) == 0);
            }
        }
        i = i + 1;
    }
    
    assert(row_invariant(dp@, 0, k as nat));
    
    // Build Pascal's triangle row by row up to row n
    let mut row: u64 = 1;
    while row <= n
        invariant
            1 <= row <= n + 1,
            dp.len() == (k + 1) as usize,
            row_invariant(dp@, (row - 1) as nat, k as nat)
    {
        // Process current row from right to left to avoid overwriting needed values
        let mut j: u64 = if row <= k { row } else { k };
        
        // First, handle the C(row, row) case if row <= k
        if row <= k {
            assert(j == row);
            dp.set(row as usize, 1);
            proof {
                comb_n_n(row as nat);
                assert(comb(row as nat, row as nat) == 1);
            }
            j = row - 1;
        }
        
        while j >= 1
            invariant
                j <= if row <= k { row - 1 } else { k as int },
                dp.len() == (k + 1) as usize,
                // Elements to the right of j are already updated for row `row`
                forall|idx: nat| j < idx <= k.min(row) as nat ==> 
                    #[trigger] dp@[idx as int] == comb(row as nat, idx),
                // Elements at and to the left of j still have values from row `row - 1`
                forall|idx: nat| idx <= j && idx <= ((row - 1) as int).min(k as int) as nat ==> 
                    #[trigger] dp@[idx as int] == comb((row - 1) as nat, idx)
        {
            assert(j <= k);
            assert(j < row); // Since we start from row-1 or k, and row >= 1
            
            let left_val = dp[(j - 1) as usize];
            let curr_val = dp[j as usize];
            
            proof {
                assert(j - 1 <= ((row - 1) as int).min(k as int) as nat);
                assert(j <= ((row - 1) as int).min(k as int) as nat);
                assert(left_val == comb((row - 1) as nat, (j - 1) as nat));
                assert(curr_val == comb((row - 1) as nat, j as nat));
                pascal_identity(row as nat, j as nat);
            }
            
            dp.set(j as usize, left_val + curr_val);
            
            assert(dp@[j as int] == comb(row as nat, j as nat));
            
            j = j - 1;
        }
        
        // j == 0 case: C(row, 0) = 1 (already correct from previous row)
        proof {
            comb_n_0(row as nat);
            comb_n_0((row - 1) as nat);
            assert(dp@[0] == comb((row - 1) as nat, 0));
            assert(dp@[0] == 1);
            assert(dp@[0] == comb(row as nat, 0));
        }
        
        assert(row_invariant(dp@, row as nat, k as nat));
        
        row = row + 1;
    }
    
    assert(row == n + 1);
    assert(row_invariant(dp@, n as nat, k as nat));
    
    dp[k as usize]
}
// </vc-code>

fn main() {}

}