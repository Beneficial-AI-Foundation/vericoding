use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Factorial(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        n * Factorial(n - 1)
    }
}

fn IterativeFactorial(n: nat) -> (result: nat)
    ensures
        result == Factorial(n)
{
    let mut i: nat = 0;
    let mut fact: nat = 1;
    
    while i < n
        invariant
            i <= n,
            fact == Factorial(i),
        decreases
            n - i,
    {
        // Store the old value of i for the proof
        let old_i = i;
        i = i + 1;
        fact = fact * i;
        
        // Prove that the invariant is maintained
        assert(i == old_i + 1);
        assert(i > 0); // Since we incremented i and were in the loop
        assert(fact == Factorial(old_i) * i) by {
            // fact was updated to old_fact * i, and old_fact == Factorial(old_i)
        }
        assert(Factorial(i) == i * Factorial(i - 1)) by {
            // This follows from the definition of Factorial since i > 0
        }
        assert(i - 1 == old_i);
        assert(fact == Factorial(i)) by {
            // fact == Factorial(old_i) * i == Factorial(i - 1) * i == Factorial(i)
        }
    }
    
    fact
}

}