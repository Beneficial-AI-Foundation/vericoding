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
        proof {
            // We need to show that fact == Factorial(i) after the updates
            // Before updates: old_fact == Factorial(old_i) where old_i = i - 1
            // After updates: fact = old_fact * i and we want fact == Factorial(i)
            
            // Since i > 0 (because we're in the loop), Factorial(i) = i * Factorial(i-1)
            assert(i > 0);
            assert(Factorial(i) == i * Factorial(i - 1));
            // The old value of fact was Factorial(i-1), and we multiplied by i
            // So now fact == i * Factorial(i-1) == Factorial(i)
        }
    }
    
    fact
}

}