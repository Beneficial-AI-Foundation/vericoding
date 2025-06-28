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
        i = i + 1;
        fact = fact * i;
        
        // Prove that the invariant is maintained
        assert(i > 0); // Since we incremented i and were in the loop
        assert(Factorial(i) == i * Factorial(i - 1)) by {
            // This follows from the definition of Factorial since i > 0
        }
        // Before the updates: old_fact == Factorial(old_i) where old_i = i - 1
        // After the updates: fact = old_fact * i = Factorial(i - 1) * i = Factorial(i)
    }
    
    fact
}

}