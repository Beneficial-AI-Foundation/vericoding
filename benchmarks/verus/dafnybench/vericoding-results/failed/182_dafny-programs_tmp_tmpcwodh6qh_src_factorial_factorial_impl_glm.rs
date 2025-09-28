use vstd::prelude::*;

verus! {

spec fn fact(n: nat) -> nat 
    decreases n
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}

// <vc-helpers>
proof fn fact_recurrence(n: nat)
    requires n > 0,
    ensures fact(n) == n * fact(n - 1)
{
    assert(fact(n) == n * fact((n - 1) as nat));
    assert((n-1) as nat == n-1);
    assert(fact((n-1) as nat) == fact(n-1));
}
// </vc-helpers>

// <vc-spec>
fn factorial(n: u32) -> (res: u32)
    requires n <= 12  // to prevent overflow
    ensures res == fact(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        1u32
    } else {
        let mut i: u32 = 1;
        let mut res: u32 = 1;
        
        while (i < n)
            invariant 1 <= i
            invariant i <= n
            invariant res == fact(i as nat)
        {
            i = i + 1;
            let old_res = res;
            res = res * i;
            
            proof {
                assert(old_res == fact((i - 1) as nat));
                fact_recurrence(i as nat);
                assert(res == old_res * i);
                assert(res == fact(i as nat));
            }
        }
        res
    }
}
// </vc-code>

fn main() {}

}