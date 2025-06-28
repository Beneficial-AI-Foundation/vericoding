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
        // Before the loop body: fact == Factorial(i) and i < n
        // We want to update both i and fact so that fact == Factorial(i+1)
        
        // First, compute the new factorial value
        let new_i = i + 1;
        let new_fact = fact * new_i;
        
        // Prove that new_fact == Factorial(new_i)
        assert(fact == Factorial(i));
        assert(new_i == i + 1);
        assert(new_i > 0);
        assert(Factorial(new_i) == new_i * Factorial(new_i - 1));
        assert(new_i - 1 == i);
        assert(Factorial(new_i) == new_i * Factorial(i));
        assert(new_fact == fact * new_i);
        assert(new_fact == Factorial(i) * new_i);
        assert(new_fact == new_i * Factorial(i));
        assert(new_fact == Factorial(new_i));
        
        // Now update the variables
        i = new_i;
        fact = new_fact;
        
        // The invariant is preserved: fact == Factorial(i)
    }
    
    // After the loop: i >= n and i <= n, so i == n
    // And fact == Factorial(i) == Factorial(n)
    assert(i == n);
    assert(fact == Factorial(n));
    
    fact
}

}