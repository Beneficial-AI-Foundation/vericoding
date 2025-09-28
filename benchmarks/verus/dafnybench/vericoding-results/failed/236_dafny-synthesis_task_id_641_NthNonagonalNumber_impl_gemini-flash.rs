use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nth_nonagonal_number(n: int) -> (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
// </vc-spec>
// <vc-code>
{
    let term1: int = n;
    let term2: int = (7 * n - 5);
    let product_numerator: int = term1 * term2;

    proof {
        // Assertions for checking type inference and basic arithmetic
        assert((7 * n - 5) == 7 * n - 5); 

        // Prove product_numerator is even
        if n % 2 == 0 {
            // n is even, so product_numerator (n * term2) is even
            assert(product_numerator % 2 == 0);
        } else {
            // n is odd
            // (7 * n - 5) % 2
            // Since n is odd, n = 2k + 1 for some integer k
            // 7n - 5 = 7(2k + 1) - 5 = 14k + 7 - 5 = 14k + 2
            // Which is always even.
            assert((7 * n - 5) % 2 == 0);
            assert(term2 % 2 == 0); // term2 is even
            assert(product_numerator % 2 == (n * term2) % 2);
            assert(product_numerator % 2 == (n % 2 * term2 % 2) % 2); // (odd * even) is even
            assert(product_numerator % 2 == (1 * 0) % 2); // 1 (odd) * 0 (even) = 0
            assert(product_numerator % 2 == 0);
        }
    }

    let result: int = product_numerator / 2;

    result
}
// </vc-code>

fn main() {}

}