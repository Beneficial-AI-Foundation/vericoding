use vstd::prelude::*;

verus! {

// recursive definition of factorial
spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

// iterative implementation of factorial

// <vc-helpers>
// Lemma to help prove the loop invariant
proof fn factorial_step_lemma(i: nat, acc: nat)
    requires i > 0,
    ensures acc * factorial(i) == (acc * i) * factorial((i - 1) as nat)
{
    assert(factorial(i) == i * factorial((i - 1) as nat));
    // The postcondition follows from the definition of factorial
    // acc * factorial(i) == acc * (i * factorial((i - 1) as nat))
    // == (acc * i) * factorial((i - 1) as nat)
}
// </vc-helpers>

// <vc-spec>
fn iterative_factorial(n: u32) -> (result: u32)
    requires n < 13, // prevent overflow
    ensures result == factorial(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut result = 1u32;
    let mut i = n;
    
    while i > 0
        invariant 
            result <= u32::MAX,
            i <= n,
            result * factorial(i as nat) == factorial(n as nat)
        decreases i
    {
        let old_result = result;
        let old_i = i;
        
        result = result * i;
        i = i - 1;
        
        proof {
            factorial_step_lemma(old_i as nat, old_result as nat);
            assert(old_result * factorial(old_i as nat) == factorial(n as nat));
            assert(result == (old_result * old_i) as u32);
            assert(i == old_i - 1);
            assert(old_i as nat > 0);
            assert(factorial(old_i as nat) == old_i * factorial((old_i - 1) as nat));
            assert(old_result as nat * factorial(old_i as nat) == (old_result as nat * old_i as nat) * factorial((old_i - 1) as nat));
            assert(result as nat * factorial(i as nat) == old_result as nat * factorial(old_i as nat));
            assert(result as nat * factorial(i as nat) == factorial(n as nat));
            assert(result * factorial(i as nat) == factorial(n as nat));
        }
    }
    
    result
}
// </vc-code>

fn main() {}

}