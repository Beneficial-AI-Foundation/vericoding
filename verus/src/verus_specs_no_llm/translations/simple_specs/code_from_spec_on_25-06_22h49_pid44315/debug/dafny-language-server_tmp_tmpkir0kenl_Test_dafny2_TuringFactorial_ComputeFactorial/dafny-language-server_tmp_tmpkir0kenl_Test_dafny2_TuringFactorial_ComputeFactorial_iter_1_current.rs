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
        n * prev
    }
}

}