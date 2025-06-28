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
                // Before the update, we have result == factorial(i - 1)
                // We want to show that after result := result * i, we have result == factorial(i)
                // Since factorial(i) == i * factorial(i - 1) when i > 0
                assert(i > 0);
                assert(factorial(i) == i * factorial(i - 1));
            }
            result = result * i;
            i = i + 1;
        }
        result
    }
}

}