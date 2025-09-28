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
proof fn lemma_comb_bound(n: nat, k: nat)
    requires 0 <= k <= n
    ensures comb(n, k) >= 1
    decreases n
{
    if n >= 1 && k >= 1 {
        lemma_comb_bound((n - 1) as nat, k);
        lemma_comb_bound((n - 1) as nat, (k - 1) as nat);
    }
}

spec fn comb_dp_table(n: nat, k: nat) -> Seq<Seq<nat>> {
    Seq::new(n + 1, |i: int| {
        let i_nat = i as nat;
        Seq::new(i_nat + 1, |j: int| {
            let j_nat = j as nat;
            if j_nat == 0 || j_nat == i_nat {
                1
            } else if j_nat > i_nat {
                0
            } else {
                comb(i_nat, j_nat)
            }
        })
    })
}

proof fn lemma_comb_dp_correct(n: nat, k: nat)
    requires 0 <= k <= n
    ensures 
        forall|i: nat, j: nat| i <= n && j <= i ==> #[trigger] comb_dp_table(n, k)@[i]@[j] == comb(i, j)
    decreases n
{
    lemma_comb_dp_correct_inner(n, k, n);
}

proof fn lemma_comb_dp_correct_inner(n: nat, k: nat, i: nat)
    requires 
        0 <= k <= n,
        i <= n
    ensures 
        forall|j: nat| j <= i ==> #[trigger] comb_dp_table(n, k)@[i]@[j] == comb(i, j)
    decreases i
{
    if i > 0 {
        lemma_comb_dp_correct_inner(n, k, (i - 1) as nat);
    }
    
    assert forall|j: nat| j <= i implies comb_dp_table(n, k)@[i]@[j] == comb(i, j) by {
        let j_nat = j;
        if j_nat <= i {
            if j_nat == 0 || j_nat == i {
                assert(comb_dp_table(n, k)@[i]@[j_nat] == 1);
                assert(comb(i, j_nat) == 1);
            } else {
                assert(comb_dp_table(n, k)@[i]@[j_nat] == comb_dp_table(n, k)@[(i - 1) as nat]@[j_nat] + comb_dp_table(n, k)@[(i - 1) as nat]@[(j_nat - 1) as nat]);
                assert(comb_dp_table(n, k)@[(i - 1) as nat]@[j_nat] == comb((i - 1) as nat, j_nat));
                assert(comb_dp_table(n, k)@[(i - 1) as nat]@[(j_nat - 1) as nat] == comb((i - 1) as nat, (j_nat - 1) as nat));
                assert(comb(i, j_nat) == comb((i - 1) as nat, j_nat) + comb((i - 1) as nat, (j_nat - 1) as nat));
            }
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn Comb(n: u64, k: u64) -> (res: u64)
    requires 0 <= k <= n
    ensures res == comb(n as nat, k as nat)
// </vc-spec>
// <vc-code>
{
    let mut dp: Vec<Vec<u64>> = Vec::new();
    
    let n_usize = n as usize;
    let k_usize = k as usize;
    
    proof { lemma_comb_bound(n as nat, k as nat); }
    
    let mut i: u64 = 0;
    while i <= n
        invariant
            0 <= i <= n + 1,
            dp.len() == i as usize,
            forall|row: int| 0 <= row < i ==> {
                let row_nat = row as nat;
                dp@[row].len() == (row_nat + 1) as usize,
                forall|col: int| 0 <= col <= row_nat ==> 
                    dp@[row]@[col] as nat == comb(row_nat, col as nat)
            }
    {
        let mut row: Vec<u64> = Vec::new();
        let mut j: u64 = 0;
        
        while j <= i
            invariant
                0 <= j <= i + 1,
                row.len() == j as usize,
                forall|col: int| 0 <= col < j ==> {
                    let col_nat = col as nat;
                    row@[col] as nat == comb(i as nat, col_nat)
                }
        {
            if j == 0 || j == i {
                row.push(1);
            } else {
                let prev_row = &dp[(i - 1) as usize];
                let val = prev_row[j as usize] + prev_row[(j - 1) as usize];
                row.push(val);
            }
            j += 1;
        }
        
        dp.push(row);
        i += 1;
    }
    
    proof { lemma_comb_dp_correct(n as nat, k as nat); }
    
    dp[n_usize][k_usize]
}
// </vc-code>

fn main() {}

}