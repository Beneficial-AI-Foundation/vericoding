#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

spec fn arith_sum_int(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { i + arith_sum_int( (i - 1) as nat) }
}

proof fn lemma_arith_sum_monotonic(i: nat, j:nat)
    requires
        i <= j,
    ensures
        arith_sum_int(i as nat) <= arith_sum_int(j as nat),
    decreases j
{
    if i == j {
        // Base case: i == j, so arith_sum_int(i) == arith_sum_int(j)
    } else {
        // i < j, so we can use induction
        if j > 0 {
            // j > 0, so arith_sum_int(j) = j + arith_sum_int(j-1)
            // We know i <= j-1 (since i < j and both are nat)
            if i <= j - 1 {
                lemma_arith_sum_monotonic(i, (j - 1) as nat);
                // Now we know arith_sum_int(i) <= arith_sum_int(j-1)
                // And arith_sum_int(j) = j + arith_sum_int(j-1) >= arith_sum_int(j-1)
                // So arith_sum_int(i) <= arith_sum_int(j-1) <= arith_sum_int(j)
            }
        }
    }
}

fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        arith_sum_int(n as nat) < 10000,
    ensures
        arith_sum_int(n as nat) == sum,
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < n
        invariant
            i <= n,
            sum == arith_sum_int(i as nat),
        decreases n - i
    {
        i = i + 1;
        sum = sum + i;
    }
    
    sum
}

} // verus!