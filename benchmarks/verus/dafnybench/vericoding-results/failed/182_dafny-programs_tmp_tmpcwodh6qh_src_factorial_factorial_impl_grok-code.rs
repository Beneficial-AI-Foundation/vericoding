use vstd::prelude::*;

verus! {

spec fn fact(n: nat) -> nat 
    decreases n
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}

// <vc-helpers>
spec fn my_fact(n: nat) -> u64
    decreases n
{
    if n == 0 { 1 } else { (n as u64) * my_fact(n - 1) }
}

proof fn my_fact_matches_fact(n: nat)
    requires n <= 12
    ensures my_fact(n) == fact(n) as u64
    decreases n
{
    if n == 0 {
    } else {
        let prev_match = my_fact_matches_fact(n - 1);
        assert((n as u64) * my_fact(n - 1) == (n as u64) * (fact(n - 1) as u64));
        assert(fact(n) == n * fact(n - 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn factorial(n: u32) -> (res: u32)
    requires n <= 12  // to prevent overflow
    ensures res == fact(n as nat)
// </vc-spec>
// <vc-code>
{
    proof {
        assert(n as nat > 0 ==> fact(n as nat) == (n as nat) * fact((n - 1) as nat));
    }
    let mut res: u32 = 1;
    let mut i: u32 = 0;
    while i < n
        invariant
            i <= n,
            res == fact(i as nat),
        decreases n - i,
    {
        assert(i < n);
        let temp = res as u64;
        let next = (i as u64 + 1);
        res = (temp * next) as u32;
        i += 1;
    }
    res
}
// </vc-code>

fn main() {}

}