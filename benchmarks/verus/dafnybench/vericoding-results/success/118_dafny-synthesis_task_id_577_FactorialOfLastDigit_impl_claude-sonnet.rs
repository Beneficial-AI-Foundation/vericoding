use vstd::prelude::*;

verus! {

spec fn factorial(n: int) -> int
    recommends n >= 0
    decreases n when n >= 0
{
    if n == 0 { 1 } else { n * factorial((n - 1) as int) }
}

// <vc-helpers>
proof fn factorial_small_values()
    ensures factorial(0) == 1,
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
    assert(factorial(0) == 1);
    assert(factorial(1) == 1 * factorial(0) == 1 * 1 == 1);
    assert(factorial(2) == 2 * factorial(1) == 2 * 1 == 2);
    assert(factorial(3) == 3 * factorial(2) == 3 * 2 == 6);
    assert(factorial(4) == 4 * factorial(3) == 4 * 6 == 24);
    assert(factorial(5) == 5 * factorial(4) == 5 * 24 == 120);
    assert(factorial(6) == 6 * factorial(5) == 6 * 120 == 720);
    assert(factorial(7) == 7 * factorial(6) == 7 * 720 == 5040);
    assert(factorial(8) == 8 * factorial(7) == 8 * 5040 == 40320);
    assert(factorial(9) == 9 * factorial(8) == 9 * 40320 == 362880);
}

proof fn mod_10_bounds(n: u64)
    ensures 0 <= (n % 10) <= 9
{
}

fn factorial_digit(d: u64) -> (fact: u64)
    requires 0 <= d <= 9
    ensures fact == factorial(d as int)
{
    proof { factorial_small_values(); }
    
    if d == 0 { 1 }
    else if d == 1 { 1 }
    else if d == 2 { 2 }
    else if d == 3 { 6 }
    else if d == 4 { 24 }
    else if d == 5 { 120 }
    else if d == 6 { 720 }
    else if d == 7 { 5040 }
    else if d == 8 { 40320 }
    else { 362880 }
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
    proof { mod_10_bounds(n); }
    factorial_digit(last_digit)
}
// </vc-code>

fn main() {
}

}