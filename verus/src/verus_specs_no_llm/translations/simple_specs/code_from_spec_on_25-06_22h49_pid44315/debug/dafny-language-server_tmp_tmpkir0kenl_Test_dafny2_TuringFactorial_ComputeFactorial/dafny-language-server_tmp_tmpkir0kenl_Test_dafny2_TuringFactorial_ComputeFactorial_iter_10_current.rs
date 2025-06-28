use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Factorial(n: int) -> int
    decreases n
{
    if n <= 1 {
        1
    } else {
        n * Factorial(n - 1)
    }
}

fn ComputeFactorial(n: int) -> (u: int)
    requires
        1 <= n
    ensures
        u == Factorial(n)
    decreases n
{
    if n == 1 {
        1
    } else {
        let prev = ComputeFactorial(n - 1);
        let result = n * prev;
        
        // Prove that result equals Factorial(n)
        assert(prev == Factorial(n - 1)); // from postcondition of recursive call
        assert(result == n * prev);       // by definition of result
        assert(result == n * Factorial(n - 1)); // by substitution
        
        // Since n > 1, by definition of Factorial: Factorial(n) == n * Factorial(n - 1)
        assert(n > 1); // since n >= 1 and n != 1
        assert(Factorial(n) == n * Factorial(n - 1)); // by definition of Factorial when n > 1
        
        // Therefore result == Factorial(n)
        assert(result == Factorial(n)); // by transitivity
        
        result
    }
}

}