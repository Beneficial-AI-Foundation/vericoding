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
        assert(n > 1);
        assert(n - 1 >= 1);
        let prev = ComputeFactorial(n - 1);
        assert(prev == Factorial(n - 1));
        let result = n * prev;
        assert(result == n * Factorial(n - 1));
        // Help Verus understand the recursive definition
        assert(Factorial(n) == n * Factorial(n - 1)) by {
            // The definition of Factorial when n > 1
        };
        assert(result == Factorial(n));
        result
    }
}

}