verus! {

use builtin::*;
use builtin_macros::*;

fn main() {
}

spec fn odd(n: nat) -> bool {
    n % 2 == 1
}

spec fn even(n: nat) -> bool {
    n % 2 == 0
}

// Helper lemma to prove properties about odd and even
proof fn lemma_odd_even_exclusive(n: nat)
    ensures odd(n) ==> !even(n),
    ensures even(n) ==> !odd(n),
{
    // Use the fundamental property that for any natural number n,
    // n % 2 must be either 0 or 1
    assert(n % 2 < 2);
    
    if odd(n) {
        assert(n % 2 == 1);
        // Since n % 2 == 1, it cannot be 0
        assert(n % 2 != 0);
        assert(!even(n));
    }
    
    if even(n) {
        assert(n % 2 == 0);
        // Since n % 2 == 0, it cannot be 1
        assert(n % 2 != 1);
        assert(!odd(n));
    }
}

// Helper lemma to prove that every natural number is either odd or even
proof fn lemma_odd_or_even(n: nat)
    ensures odd(n) || even(n),
{
    // For any natural number n, n % 2 must be less than 2
    assert(n % 2 < 2);
    
    // Since n % 2 is a natural number less than 2, it must be 0 or 1
    if n % 2 == 0 {
        assert(even(n));
        assert(odd(n) || even(n));
    } else {
        // Since n % 2 < 2 and n % 2 != 0, we must have n % 2 == 1
        assert(n % 2 == 1);
        assert(odd(n));
        assert(odd(n) || even(n));
    }
}

}