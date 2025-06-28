use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Factorial(n: int) -> int
    decreases n via Factorial_decreases
{
    if n <= 1 {
        1
    } else {
        n * Factorial(n - 1)
    }
}

proof fn Factorial_decreases(n: int) {
    if n > 1 {
        assert(n - 1 < n);
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
        let prev = ComputeFactorial(n - 1);
        assert(prev == Factorial(n - 1));
        let result = n * prev;
        assert(result == n * Factorial(n - 1));
        assert(Factorial(n) == n * Factorial(n - 1));
        assert(result == Factorial(n));
        result
    }
}

}