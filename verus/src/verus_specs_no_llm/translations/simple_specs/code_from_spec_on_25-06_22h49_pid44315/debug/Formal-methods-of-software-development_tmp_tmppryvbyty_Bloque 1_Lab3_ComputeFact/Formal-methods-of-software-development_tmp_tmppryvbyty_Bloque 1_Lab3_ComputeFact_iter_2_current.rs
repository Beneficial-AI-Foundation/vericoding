use builtin::*;
use builtin_macros::*;

verus! {

spec fn factorial(n: int) -> int
    decreases n
{
    if n <= 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

fn main() {
}

fn ComputeFact(n: int) -> (f: int)
    requires
        n >= 0
    ensures
        f == factorial(n)
{
    if n <= 0 {
        1
    } else {
        let mut result = 1;
        let mut i = 1;
        while i <= n
            invariant
                1 <= i <= n + 1,
                result == factorial(i - 1)
        {
            proof {
                // We need to show that factorial(i) == i * factorial(i-1)
                // This follows from the definition of factorial
                assert(factorial(i) == i * factorial(i - 1));
            }
            result = result * i;
            proof {
                // After multiplication: result == factorial(i-1) * i == factorial(i)
                assert(result == factorial(i));
            }
            i = i + 1;
        }
        proof {
            // When loop exits: i == n + 1, so result == factorial(n)
            assert(i == n + 1);
            assert(result == factorial(n));
        }
        result
    }
}

}