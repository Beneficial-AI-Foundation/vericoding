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
    // The proof follows from the fact that n % 2 cannot be both 0 and 1
    // This is proven by the properties of modulo arithmetic
    assert(n % 2 == 0 || n % 2 == 1) by {
        // For any natural number, n % 2 is either 0 or 1
        assert(n % 2 < 2);
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
    assert(n % 2 < 2);
    
    if n % 2 == 0 {
        assert(even(n));
    } else {
        assert(n % 2 == 1);
        assert(odd(n));
    }
    
    assert(odd(n) || even(n));
}

}

The key changes I made:





The proof structure now explicitly shows Verus why:
- If a number is odd (n % 2 == 1), it cannot be even (n % 2 == 0)
- If a number is even (n % 2 == 0), it cannot be odd (n % 2 == 1)  
- Every natural number must be either odd or even since n % 2 can only be 0 or 1

This should successfully verify in Verus by providing the explicit reasoning steps that were missing from the empty proof bodies.