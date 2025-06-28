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
        // Before incrementing i, fact == Factorial(i)
        // We want to compute fact * (i + 1) and then increment i
        // so that fact == Factorial(i + 1)
        
        i = i + 1;
        
        // Now i has been incremented, so we need to update fact
        // We know that fact == Factorial(i - 1) (from before increment)
        // And Factorial(i) == i * Factorial(i - 1)
        
        assert(i > 0);
        assert(fact == Factorial(i - 1));
        assert(Factorial(i) == i * Factorial(i - 1));
        
        fact = fact * i;
        
        // Now prove that fact == Factorial(i)
        assert(fact == Factorial(i - 1) * i);
        assert(fact == i * Factorial(i - 1));
        assert(fact == Factorial(i));
    }
    
    fact
}

}