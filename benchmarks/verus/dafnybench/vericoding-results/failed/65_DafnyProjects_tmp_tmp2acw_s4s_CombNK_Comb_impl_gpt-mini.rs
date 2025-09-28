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
proof fn lemma_comb_pascal(n: nat, k: nat)
    requires n >= 1 && k >= 1
    ensures comb(n, k) == comb(n - 1, k) + comb(n - 1, k - 1)
{
    // Unfolding the definition of comb yields the Pascal equality directly.
    assert(comb(n, k) == comb(n - 1, k) + comb(n - 1, k - 1));
}
// </vc-helpers>

// <vc-spec>
fn Comb(n: u64, k: u64) -> (res: u64)
    requires 0 <= k <= n
    ensures res == comb(n as nat, k as nat)
// </vc-spec>
// <vc-code>
{
    // Dynamic programming using a single row of Pascal's triangle (space optimized).
    let mut row: Vec<u64> = Vec::new();
    let ku: usize = (k as usize) + 1usize;
    let ku_nat: nat = ku as nat;

    // Initialize row with ku zeros using an explicit counter to avoid problematic invariants on row.len().
    let mut t: usize = 0usize;
    while t < ku
        invariant t <= ku
        invariant row.len() == t
        decreases (ku - t) as nat
    {
        row.push(0);
        t += 1;
    }

    // Set row[0] = 1 to represent comb(0,0) = 1.
    row.update(0, 1u64);

    // p describes the current row index such that row@[j] == comb(p, j) for 0 <= j <= min(p,k), and row@[j]==0 for j>p.
    let mut p: u64 = 0;
    while p < n
        invariant 0 <= p && p <= n
        invariant forall |idx: nat| (idx <= (if p < k { p as nat } else { k as nat }) ==> row@[idx] == comb(p as nat, idx))
        invariant forall |idx: nat| ((idx > (if p < k { p as nat } else { k as nat }) && idx < ku_nat) ==> row@[idx] == 0)
        decreases (n - p) as nat
    {
        let i: u64 = p + 1; // new row index to compute
        // upto = min(i, k)
        let upto_u64 = if i < k { i } else { k };
        let upto: usize = upto_u64 as usize;
        let upto_nat: nat = upto as nat;

        // Update from j = upto down to 1: row[j] = row[j] + row[j-1]
        let mut j: usize = upto;
        while j > 0
            invariant j <= upto
            invariant forall |idx: nat| ((idx > (j as nat) && idx <= upto_nat) ==> row@[idx] == comb(i as nat, idx))
            invariant forall |idx: nat| (idx <= (j as nat) ==> row@[idx] == comb(p as nat, idx))
            invariant forall |idx: nat| ((idx > upto_nat && idx < ku_nat) ==> row@[idx] == 0)
            decreases (j as nat)
        {
            // Compute new value for row[j] := row[j] + row[j-1]
            let old_j_val: u64 = row@[(j as nat)];
            let old_jm1_val: u64 = row@[((j - 1) as nat)];
            let new_val: u64 = old_j_val + old_jm1_val;
            row.update(j, new_val);

            // Prove that the updated entry equals comb(i, j)
            proof {
                let j_nat: nat = j as nat;
                let i_nat: nat = i as nat;
                // j >= 1 because loop condition j > 0
                assert(j >= 1);
                // i = p + 1 so i >= 1
                assert(i >= 1);
                // Use Pascal lemma for comb(i, j)
                lemma_comb_pascal(i_nat, j_nat);
                assert(comb(i_nat, j_nat) == comb((i - 1) as nat, j_nat) + comb((i - 1) as nat, j_nat - 1));
                // From the inner invariant before update, row@[j] == comb(p, j) and row@[j-1] == comb(p, j-1).
                assert(p + 1 == i);
                assert(old_j_val == comb((i - 1) as nat, j_nat));
                assert(old_jm1_val == comb((i - 1) as nat, j_nat - 1));
                // So new_val equals comb(i, j)
                assert(new_val == comb(i_nat, j_nat));
                // After row.update, the vector reflects the new value at index j
                assert(row@[j_nat] == comb(i_nat, j_nat));
            }

            j -= 1;
        }

        // After finishing inner loop, ensure row@[0] == comb(i,0) (which is 1) remains true.
        // Update p to i.
        p = i;
    }

    // At this point p == n and row@[k] == comb(n, k). Return the runtime value stored in row[k].
    proof {
        assert(row@[k as nat] == comb(n as nat, k as nat));
    }
    let res: u64 = row[k as usize];
    res
}
// </vc-code>

fn main() {}

}