use vstd::prelude::*;

verus! {

spec fn C(n: nat) -> nat
    decreases n
{
    if n == 0 { 
        1nat 
    } else { 
        ((4 * (n as int) - 2) * (C((n - 1) as nat) as int) / ((n as int) + 1)) as nat
    }
}

// <vc-helpers>
spec fn C_iterative_invariant(i: nat, current: nat, n: nat) -> bool {
    i <= n && current == C(i)
}

proof fn lemma_C_step(i: nat)
    requires i > 0
    ensures C(i) == ((4 * (i as int) - 2) * (C((i - 1) as nat) as int) / ((i as int) + 1)) as nat
{
    // This follows directly from the definition of C
}

proof fn lemma_C_base()
    ensures C(0) == 1
{
    // This follows directly from the definition of C
}

proof fn lemma_arithmetic_bounds(i: u64, n: u64)
    requires i <= n && n < 100  // reasonable upper bound
    requires i > 0
    ensures 4 * (i as int) >= 2
    ensures 4 * (i as int) - 2 >= 0
{
}
// </vc-helpers>

// <vc-spec>
fn calcC(n: u64) -> (res: u64)
    ensures res == C(n as nat),
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 1;
    }
    
    let mut i: u64 = 1;
    let mut current: u64 = 1;
    
    while i <= n
        invariant
            i <= n + 1,
            current == C((i - 1) as nat),
            i > 0,
            i >= 1,
            4 * i >= 2,
        decreases n - i + 1,
    {
        assert(4 * i >= 2);
        assert(i >= 1);
        let four_i = 4u64 * i;
        assert(four_i >= 2);
        let numerator = (four_i - 2) * current;
        current = numerator / (i + 1);
        
        assert(current == C(i as nat)) by {
            lemma_C_step(i as nat);
        };
        
        i = i + 1;
    }
    
    current
}
// </vc-code>

fn main() {}

}