use vstd::prelude::*;

verus! {

spec fn fact(n: nat) -> nat 
    decreases n
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}

// <vc-helpers>
proof fn fact_0() 
    ensures fact(0) == 1
{
}

proof fn fact_step(n: nat) 
    requires n >= 1
    ensures fact(n) == n * fact((n - 1) as nat)
{
}

proof fn fact_unfold(n: nat)
    ensures 
        n == 0 ==> fact(n) == 1,
        n >= 1 ==> fact(n) == n * fact((n - 1) as nat)
{
    if n == 0 {
    } else {
    }
}

proof fn fact_monotonic(n: nat, m: nat)
    requires n <= m
    ensures fact(n) <= fact(m)
    decreases m
{
    if n < m {
        fact_monotonic(n, (m - 1) as nat);
        assert(fact(m) == m * fact((m - 1) as nat)) by {
            fact_unfold(m);
        };
        assert(fact((m - 1) as nat) <= fact(m)) by {
            assert(m >= 1) by {
                assert(n <= m);
                assert(n < m);
            };
        };
        assert(fact(n) <= fact((m - 1) as nat));
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
    let mut res: u32 = 1;
    let mut i: u32 = 1;
    
    proof {
        fact_unfold(0);
    }
    
    while i <= n
        invariant
            i <= n + 1,
            i >= 1,
            res == fact(i as nat),
            res as nat <= fact(n as nat),
        decreases (n - i) as int
    {
        assert(res as nat == fact(i as nat));
        
        let old_res = res;
        let old_i = i;
        
        if i < n {
            proof {
                fact_monotonic(i as nat, n as nat);
                assert(fact(i as nat) <= fact(n as nat));
            }
        }
        
        if i < n {
            proof {
                assert((i + 1) as nat >= 1);
                fact_unfold((i + 1) as nat);
                assert(fact((i + 1) as nat) == (i + 1) as nat * fact(i as nat));
            }
            
            res = res.checked_mul(i + 1).expect("overflow");
            i = i + 1;
            
            proof {
                assert(res as nat == old_res as nat * (i as nat));
                assert(old_res as nat == fact(old_i as nat));
                assert(old_i == i - 1);
                assert(res as nat == (i as nat) * fact((i - 1) as nat));
                assert(res as nat == fact(i as nat));
            }
        } else {
            i = i + 1;
        }
    }
    res
}
// </vc-code>

fn main() {}

}