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
proof fn comb_summands_positive(n: nat, k: nat)
    requires 0 <= k <= n
    ensures comb(n as nat, k as nat) >= 1
{
    if n == 0 {
        assert(k == 0);
        assert(comb(0, 0) == 1);
    } else if k == 0 {
        assert(comb(n, 0) == 1);
    } else if k == n {
        assert(comb(n, k) == 1);
    } else {
        assert(comb(n, k) == comb(n-1, k) + comb(n-1, k-1));
        comb_summands_positive(n-1, k);
        comb_summands_positive(n-1, k-1);
    }
}

proof fn comb_pascal_row(n: nat, k: nat)
    requires 1 <= k < n
    ensures comb(n, k) == comb(n-1, k) + comb(n-1, k-1)
{
    assert(comb(n, k) == comb(n-1, k) + comb(n-1, k-1)) by {
        reveal(comb);
    }
}

proof fn comb_pascal_boundary(n: nat, k: nat)
    requires 0 <= k <= n
    ensures (k == 0 || k == n) <==> comb(n, k) == 1
{
    if k == 0 || k == n {
        assert(comb(n, k) == 1);
    } else {
        assert(0 < k < n);
        assert(comb(n, k) >= 2) by {
            comb_summands_positive(n, k);
            comb_pascal_row(n, k);
        }
    }
}

fn comb_dp_inner(n: u64, i: u64, dp: &Vec<u64>, k: u64) -> (res: u64)
    requires 0 <= k <= n,
        0 <= i <= n,
        dp.len() == (n + 1) as usize,
        forall|j: int| 0 <= j < i ==> dp@[j as usize] == comb((i-1) as nat, j as nat)
    ensures res == comb(i as nat, k as nat)
{
    if i == 0 {
        assert(k == 0);
        assert(comb(0, 0) == 1);
        return 1;
    } else if k == i {
        assert(comb(i, k) == 1);
        return 1;
    } else if k == 0 {
        assert(comb(i, 0) == 1);
        return 1;
    } else {
        let dp_k = dp[k as usize];
        let dp_k_minus_1 = dp[(k - 1) as usize];
        let result = dp_k + dp_k_minus_1;
        
        proof {
            assert(dp_k == comb((i-1) as nat, k as nat));
            assert(dp_k_minus_1 == comb((i-1) as nat, (k-1) as nat));
            assert(result == comb((i-1) as nat, k as nat) + comb((i-1) as nat, (k-1) as nat));
            assert(comb(i as nat, k as nat) == comb((i-1) as nat, k as nat) + comb((i-1) as nat, (k-1) as nat)) by {
                reveal(comb);
            }
        }
        
        return result;
    }
}
// </vc-helpers>

// <vc-spec>
fn Comb(n: u64, k: u64) -> (res: u64)
    requires 0 <= k <= n
    ensures res == comb(n as nat, k as nat)
// </vc-spec>
// <vc-code>
{
    let mut dp = Vec::new();
    dp.push(1);
    
    for i in 1..=n
        invariant
            dp.len() == (i + 1) as usize,
            forall|j: int| 0 <= j <= i ==> dp@[j as usize] == comb(i as nat, j as nat)
    {
        dp.push(1);
        
        for j in (1..i).rev()
            invariant
                dp.len() == (i + 1) as usize,
                forall|m: int| 0 <= m <= j + 1 ==> dp@[m as usize] == comb(i as nat, m as nat),
                forall|m: int| j + 1 < m <= i ==> dp@[m as usize] == comb((i-1) as nat, m as nat)
        {
            let new_val = dp[j as usize] + dp[(j - 1) as usize];
            dp.set(j as usize, new_val);
            
            proof {
                assert(dp[j as usize] == new_val);
                assert(new_val == comb((i-1) as nat, j as nat) + comb((i-1) as nat, (j-1) as nat));
                assert(comb(i as nat, j as nat) == comb((i-1) as nat, j as nat) + comb((i-1) as nat, (j-1) as nat)) by {
                    reveal(comb);
                }
            }
        }
    }
    
    dp[k as usize]
}
// </vc-code>

fn main() {}

}