use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to prove that n * (7 * n - 5) is always even
proof fn nonagonal_divisible_by_2(n: int)
    requires n >= 0
    ensures (n * (7 * n - 5)) % 2 == 0
{
    // n * (7 * n - 5) = 7n² - 5n = n(7n - 5)
    // We need to show this is even
    
    if n % 2 == 0 {
        // If n is even, then n * anything is even
        assert(n * (7 * n - 5) % 2 == 0);
    } else {
        // If n is odd, then 7n is odd, so 7n - 5 is even
        assert(n % 2 == 1);
        assert((7 * n) % 2 == 1);
        assert((7 * n - 5) % 2 == 0);
        assert(n * (7 * n - 5) % 2 == 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn nth_nonagonal_number(n: int) -> (number: int)
    requires n >= 0
    ensures number == n * (7 * n - 5) / 2
// </vc-spec>
// <vc-code>
{
    nonagonal_divisible_by_2(n);
    let numerator: int = n * (7 * n - 5);
    assert(numerator % 2 == 0);
    let result: int = numerator / 2;
    assert(result == n * (7 * n - 5) / 2);
    result
}
// </vc-code>

fn main() {}

}