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
        
        // Proof that fact == Factorial(i) after the update
        assert(fact == Factorial(i - 1) * i);
        assert(i > 0);
        assert(Factorial(i) == i * Factorial(i - 1));
        assert(fact == Factorial(i));
    }
    
    fact
}

}