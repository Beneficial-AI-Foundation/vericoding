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
        assert(Factorial(1) == 1);
        1
    } else {
        assert(n > 1); // Help Verus understand we're in the n > 1 case
        let prev = ComputeFactorial(n - 1);
        assert(prev == Factorial(n - 1));
        let result = n * prev;
        assert(result == n * Factorial(n - 1));
        // Since n > 1, Factorial(n) = n * Factorial(n - 1) by definition
        assert(Factorial(n) == n * Factorial(n - 1)) by {
            // This follows directly from the definition of Factorial since n > 1
        };
        assert(result == Factorial(n));
        result
    }
}

}