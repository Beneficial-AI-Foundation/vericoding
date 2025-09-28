use vstd::prelude::*;

verus! {

spec fn factorial(n: int) -> int
    recommends n >= 0
    decreases n when n >= 0
{
    if n == 0 { 1 } else { n * factorial((n - 1) as int) }
}

// <vc-helpers>
// Helper lemmas to establish factorial values for small numbers
proof fn factorial_values()
    ensures
        factorial(0) == 1,
        factorial(1) == 1,
        factorial(2) == 2,
        factorial(3) == 6,
        factorial(4) == 24,
        factorial(5) == 120,
        factorial(6) == 720,
        factorial(7) == 5040,
        factorial(8) == 40320,
        factorial(9) == 362880,
{
    // These follow directly from the factorial definition
    assert(factorial(0) == 1);
    assert(factorial(1) == 1 * factorial(0) == 1);
    assert(factorial(2) == 2 * factorial(1) == 2);
    assert(factorial(3) == 3 * factorial(2) == 6);
    assert(factorial(4) == 4 * factorial(3) == 24);
    assert(factorial(5) == 5 * factorial(4) == 120);
    assert(factorial(6) == 6 * factorial(5) == 720);
    assert(factorial(7) == 7 * factorial(6) == 5040);
    assert(factorial(8) == 8 * factorial(7) == 40320);
    assert(factorial(9) == 9 * factorial(8) == 362880);
}
// </vc-helpers>

// <vc-spec>
fn factorial_of_last_digit(n: u64) -> (fact: u64)
    requires n >= 0
    ensures fact == factorial((n % 10) as int)
// </vc-spec>
// <vc-code>
{
    let last_digit = n % 10;
    
    proof {
        factorial_values();
    }
    
    match last_digit {
        0 => 1,
        1 => 1,
        2 => 2,
        3 => 6,
        4 => 24,
        5 => 120,
        6 => 720,
        7 => 5040,
        8 => 40320,
        9 => 362880,
        _ => {
            proof {
                // last_digit % 10 is always in range [0, 9]
                assert(false);
            }
            unreached()
        }
    }
}
// </vc-code>

fn main() {
}

}