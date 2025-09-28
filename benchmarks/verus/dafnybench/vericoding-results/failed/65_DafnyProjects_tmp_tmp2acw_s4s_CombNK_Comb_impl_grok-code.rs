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

spec fn dp_value(i: nat, j: nat) -> nat
    recommends j <= i || (j == 0 && i >= 0)
{
    if j > i {
        0
    } else if j == 0 {
        1
    } else if j == i {
        1
    } else {
        dp_value((i - 1) as nat, (j - 1) as nat) + dp_value((i - 1) as nat, j)
    }
}

proof fn lemma_dp_value_equals_comb(n: nat, k: nat)
    requires k <= n
    ensures dp_value(n, k) == comb(n, k)
    decreases n
{
    if k == 0 || k == n {
        // Base case handled by definition
    } else {
        lemma_dp_value_equals_comb((n - 1) as nat, (k - 1) as nat);
        lemma_dp_value_equals_comb((n - 1) as nat, k);
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
    let n_us: usize = n as usize;
    let k_us: usize = k as usize;
    let mut table: Vec<Vec<u64>> = Vec::new();
    
    #[verifier::loop_isolation(false)]
    for i in 0..(n_us + 1) {
        invariant
            table.len() == i,
            forall |idx: int| 0 <= idx < table.len() as int ==> forall |j: int| 0 <= j < table@[idx as int].len() as int ==> #[trigger] table@[idx as int][j as int] as int == dp_value(idx as nat, j as nat) as int;

        let mut row: Vec<u64> = Vec::new();
        
        for j in 0..(i + 1) {
            let val: u64 = if j == 0 {
                1
            } else if j == i {
                1
            } else {
                table[i - 1][j - 1] + table[i - 1][j]
            };
            
            assert(val as int == dp_value(i as nat, j as nat) as int);
            row.push(val);
        }
        
        table.push(row);
    }
    
    proof {
        lemma_dp_value_equals_comb(n as nat, k as nat);
        // Assertion to confirm the table value matches the spec
        assert(table@[n_us as int][k_us as int] as int == dp_value(n as nat, k as nat) as int);
        assert(dp_value(n as nat, k as nat) == comb(n as nat, k as nat));
    }
    
    table[n_us][k_us]
}
// </vc-code>

fn main() {}

}