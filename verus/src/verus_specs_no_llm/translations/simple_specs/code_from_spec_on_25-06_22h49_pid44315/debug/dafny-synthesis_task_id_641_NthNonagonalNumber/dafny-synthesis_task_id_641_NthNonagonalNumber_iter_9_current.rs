use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma to prove that n * (7*n - 5) is always even
proof fn lemma_nonagonal_even(n: int)
    requires n >= 0
    ensures (n * (7 * n - 5)) % 2 == 0
{
    // Case analysis on n modulo 2
    if n % 2 == 0 {
        // n is even, so n * anything is even
        assert((n * (7 * n - 5)) % 2 == 0);
    } else {
        // n is odd, so n % 2 == 1
        assert(n % 2 == 1);
        // When n is odd: 7*n is odd, so 7*n - 5 is even (odd - odd = even)
        // Therefore n * (7*n - 5) = odd * even = even
        let expr = 7 * n - 5;
        assert(expr % 2 == 0); // 7*n - 5 is even when n is odd
        assert((n * expr) % 2 == 0); // odd * even = even
    }
}

fn NthNonagonalNumber(n: int) -> (number: int)
    requires
        n >= 0
    ensures
        number == n * (7 * n - 5) / 2
{
    let seven_n = 7 * n;
    let inner = seven_n - 5;
    let product = n * inner;
    
    proof {
        lemma_nonagonal_even(n);
        assert(product % 2 == 0);
    }
    
    let result = product / 2;
    
    proof {
        // Now we can establish the final equality
        assert(seven_n == 7 * n);
        assert(inner == 7 * n - 5);
        assert(product == n * (7 * n - 5));
        assert(result == n * (7 * n - 5) / 2);
    }
    
    result
}

}