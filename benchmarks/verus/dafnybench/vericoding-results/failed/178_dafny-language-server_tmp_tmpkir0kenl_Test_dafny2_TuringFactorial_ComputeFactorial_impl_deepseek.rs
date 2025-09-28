use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

// <vc-helpers>
proof fn lemma_factorial_base()
    ensures factorial(0) == 1,
{
}

proof fn lemma_add_one_equals_successor_nat(i: int)
    requires 0 <= i,
    ensures (i + 1) as nat == (i as nat) + 1,
{
}

proof fn lemma_factorial_unfold(n: nat)
    requires n >= 1,
    ensures factorial(n) == n * factorial((n - 1) as nat),
{
    reveal(factorial);
}

proof fn lemma_mul_commutes(a: nat, b: nat)
    ensures a * b == b * a,
{
    reveal(mul);
}
// </vc-helpers>

// <vc-spec>
fn compute_factorial(n: i32) -> (u: i32)
    requires 1 <= n,
    ensures u == factorial(n as nat),
// </vc-spec>
// <vc-code>
{
    let mut i: i32 = 1;
    let mut result: i32 = 1;
    
    assert(result == factorial(i as nat)) by {
        lemma_factorial_base();
    };
    
    while i < n
        invariant
            1 <= i <= n,
            result == factorial(i as nat),
        decreases n - i,
    {
        let next_i = i + 1;
        let next_result = (result as u64) * (next_i as u64);
        
        assert(next_i as nat == (i as nat) + 1) by {
            lemma_add_one_equals_successor_nat(i as int);
        };
        
        proof {
            lemma_factorial_unfold(next_i as nat);
        }
        
        assert(next_result as nat == factorial(next_i as nat)) by {
            assert(factorial(next_i as nat) == (next_i as nat) * factorial(i as nat));
            assert((next_i as nat) * factorial(i as nat) == factorial(i as nat) * (next_i as nat)) by {
                lemma_mul_commutes(next_i as nat, factorial(i as nat));
            };
            assert((result as nat) == factorial(i as nat));
        };
        
        i = next_i;
        result = next_result as i32;
    }
    
    result
}
// </vc-code>

fn main() {
}

}