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
    if i<j {
        lemma_arith_sum_monotonic(i, (j-1) as nat);
    }
}

fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        arith_sum_int(n as nat) < 10000,
    ensures
        arith_sum_int(n as nat) == sum,
{
    return 0;  // TODO: Remove this line and implement the function body
}


} // verus!
