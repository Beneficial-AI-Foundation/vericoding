use vstd::prelude::*;

fn main() {}

verus! {

spec fn arith_sum_int(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { i + arith_sum_int( (i - 1) as nat) }
}

fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        arith_sum_int(n as nat) < 10000,
    ensures
        arith_sum_int(n as nat) == sum,
{
    let mut sum: u64 = 0;
    let mut i: u64 = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i <= n
        invariant
            1 <= i <= n + 1,
            sum == arith_sum_int((i - 1) as nat),
        decreases n + 1 - i
    {
        sum = sum + i;
        i = i + 1;
    }
    
    sum
}

} // verus!