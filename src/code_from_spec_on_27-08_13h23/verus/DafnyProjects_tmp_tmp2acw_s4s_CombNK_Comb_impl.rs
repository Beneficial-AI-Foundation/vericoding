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
// Helper lemma to prove properties about comb for dynamic programming
proof fn comb_symmetry(n: nat, k: nat)
    requires 0 <= k <= n
    ensures comb(n, k) == comb(n, n - k)
    decreases n
{
    if k == 0 || k == n {
        assert(comb(n, k) == 1);
        assert(comb(n, n - k) == 1);
    } else if k == 1 {
        assert(comb(n, k) == n);
        assert(comb(n, n - 1) == n);
    } else {
        comb_symmetry((n - 1) as nat, k);
        comb_symmetry((n - 1) as nat, (k - 1) as nat);
        assert(comb(n, k) == comb((n - 1) as nat, k) + comb((n - 1) as nat, (k - 1) as nat));
        assert(comb(n, n - k) == comb((n - 1) as nat, (n - k) as nat) + comb((n - 1) as nat, ((n - k) - 1) as nat));
        assert((n - k) as nat == n - k);
        assert(((n - k) - 1) as nat == (n - 1) - k);
    }
}

// Helper function to initialize a row in the DP table
fn init_row(n: u64, k: u64) -> (row: Vec<u64>)
    requires 0 <= k <= n
    ensures row.len() == (k + 1) as usize,
            forall|i: usize| i < (k + 1) as usize ==> row@[i] == if i == 0 || i as u64 == k { 1 } else { 0 }
{
    let mut row: Vec<u64> = Vec::new();
    let mut i: u64 = 0;
    while i <= k
        invariant i <= k + 1,
                  row.len() == i as usize,
                  forall|j: usize| j < i as usize ==> row@[j] == if j == 0 || j as u64 == k { 1 } else { 0 }
    {
        if i == 0 || i == k {
            row.push(1);
        } else {
            row.push(0);
        }
        i = i + 1;
    }
    row
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
fn Comb(n: u64, k: u64) -> (res: u64)
    requires 0 <= k <= n
    ensures res == comb(n as nat, k as nat)
{
    if k == 0 || k == n {
        return 1;
    }
    if k > n / 2 {
        return Comb(n, n - k);
    }
    
    let mut dp: Vec<u64> = init_row(n, k);
    let mut i: u64 = 1;
    
    while i <= n
        invariant 0 < i <= n + 1,
                  dp.len() == (k + 1) as usize,
                  forall|r: usize| r < dp.len() ==> dp@[r] == comb(if r as u64 <= i { r as nat } else { i as nat }, r as nat)
    {
        let mut j: u64 = 1;
        let prev_dp = dp.clone();
        while j <= k
            invariant 1 <= j <= k + 1,
                      dp.len() == (k + 1) as usize,
                      forall|r: usize| r < j as usize ==> dp@[r] == if r == 0 || r as u64 == k { 1 } else { prev_dp@[(r - 1) as usize] + prev_dp@[r] },
                      forall|r: usize| r >= j as usize && r < dp.len() ==> dp@[r] == prev_dp@[r]
        {
            if j == k {
                dp.set(j as usize, 1);
            } else {
                let left = dp@[(j - 1) as usize];
                let right = dp@[j as usize];
                dp.set(j as usize, left + right);
            }
            j = j + 1;
        }
        
        proof {
            let curr_dp = dp@;
            assert forall|r: usize| r < dp.len() implies curr_dp[r] == comb(i as nat, r as nat) by {
                if r == 0 || r as u64 == k {
                    assert(curr_dp[r] == 1);
                    assert(comb(i as nat, r as nat) == 1);
                } else {
                    assert(curr_dp[r] == prev_dp@[(r - 1) as usize] + prev_dp@[r]);
                    assert(prev_dp@[(r - 1) as usize] == comb((i - 1) as nat, (r - 1) as nat));
                    assert(prev_dp@[r] == comb((i - 1) as nat, r as nat));
                    assert(comb(i as nat, r as nat) == comb((i - 1) as nat, r as nat) + comb((i - 1) as nat, (r - 1) as nat));
                }
            };
        }
        i = i + 1;
    }
    dp@[k as usize]
}
// </vc-code>

fn main() {}

}