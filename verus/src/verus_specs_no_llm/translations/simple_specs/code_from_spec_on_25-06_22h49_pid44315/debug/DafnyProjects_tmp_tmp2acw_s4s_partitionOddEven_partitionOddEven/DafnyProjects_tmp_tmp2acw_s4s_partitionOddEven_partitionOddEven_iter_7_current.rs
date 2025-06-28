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
    // For any natural number n, n % 2 can only be 0 or 1
    // If n % 2 == 1, then it cannot be 0
    // If n % 2 == 0, then it cannot be 1
    assert(n % 2 == 0 || n % 2 == 1) by {
        // This follows from the definition of modular arithmetic
        // n % 2 must be in the range [0, 2), so it's either 0 or 1
    };
    
    if odd(n) {
        assert(n % 2 == 1);
        assert(n % 2 != 0);
        assert(!even(n));
    }
    
    if even(n) {
        assert(n % 2 == 0);
        assert(n % 2 != 1);
        assert(!odd(n));
    }
}

// Helper lemma to prove that every natural number is either odd or even
proof fn lemma_odd_or_even(n: nat)
    ensures odd(n) || even(n),
{
    // For any natural number n, n % 2 is either 0 or 1
    assert(n % 2 == 0 || n % 2 == 1) by {
        // This is a fundamental property of modular arithmetic
        // n % 2 must be in the range [0, 2), so it's either 0 or 1
    };
    
    if n % 2 == 0 {
        assert(even(n));
    } else {
        assert(n % 2 == 1);
        assert(odd(n));
    }
    
    assert(odd(n) || even(n));
}

}