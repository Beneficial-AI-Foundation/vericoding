#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

spec fn arith_sum_int(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { i + arith_sum_int( (i - 1) as nat) }
}

//IMPL compute_arith_sum
fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        arith_sum_int(n as nat) < 10000,
    ensures
        arith_sum_int(n as nat) == sum,
{
    /* code modified by LLM (iteration 3): handle edge case when n = 0 */
    if n == 0 {
        return 0;
    }
    
    let mut sum: u64 = 0;
    let mut i: u64 = 1;
    
    /* code modified by LLM (iteration 3): fixed invariant by ensuring sum bound after addition */
    while i <= n
        invariant
            0 <= sum,
            1 <= i <= n + 1,
            sum == arith_sum_int((i - 1) as nat),
            i <= u64::MAX,
            arith_sum_int(n as nat) < 10000,
            sum <= arith_sum_int(n as nat),
        decreases n + 1 - i,
    {
        /* code modified by LLM (iteration 3): safe arithmetic operations */
        sum = sum + i;
        i = i + 1;
    }
    
    sum
}

} // verus!