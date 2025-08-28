use vstd::prelude::*;

verus! {

spec fn factorial(n: int) -> int
    recommends n >= 0
    decreases n when n >= 0
{
    if n == 0 { 1 } else { n * factorial((n - 1) as int) }
}

// <vc-helpers>
spec fn factorial_u64(n: u64) -> u64
    recommends n <= 10
{
    if n == 0 { 1 } else { n * factorial_u64(n - 1) }
}

proof fn factorial_equiv(n: u64)
    requires n <= 10
    ensures factorial_u64(n) == factorial(n as int)
    decreases n
{
    if n == 0 {
    } else {
        factorial_equiv(n - 1);
    }
}

proof fn factorial_small_values()
    ensures factorial_u64(0) == 1
    ensures factorial_u64(1) == 1
    ensures factorial_u64(2) == 2
    ensures factorial_u64(3) == 6
    ensures factorial_u64(4) == 24
    ensures factorial_u64(5) == 120
    ensures factorial_u64(6) == 720
    ensures factorial_u64(7) == 5040
    ensures factorial_u64(8) == 40320
    ensures factorial_u64(9) == 362880
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn factorial_of_last_digit(n: u64) -> (fact: u64)
    requires n >= 0
    ensures fact == factorial((n % 10) as int)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn factorial_of_last_digit(n: u64) -> (fact: u64)
    requires n >= 0
    ensures fact == factorial((n % 10) as int)
{
    let last_digit = n % 10;
    
    proof {
        assert(last_digit <= 9);
        factorial_equiv(last_digit);
        factorial_small_values();
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
        _ => unreached(),
    }
}
// </vc-code>

fn main() {
}

}