use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn NthNonagonalNumber(n: int) -> (number: int)
    requires
        n >= 0
    ensures
        number == n * (7 * n - 5) / 2
{
    proof {
        // We need to prove that n * (7 * n - 5) is always even
        // This is true because either n is even or (7*n - 5) is even
        if n % 2 == 0 {
            // n is even, so n * (7 * n - 5) is even
            assert(n * (7 * n - 5) % 2 == 0);
        } else {
            // n is odd, so 7*n is odd, so 7*n - 5 is even
            assert((7 * n - 5) % 2 == 0);
            assert(n * (7 * n - 5) % 2 == 0);
        }
    }
    n * (7 * n - 5) / 2
}

}