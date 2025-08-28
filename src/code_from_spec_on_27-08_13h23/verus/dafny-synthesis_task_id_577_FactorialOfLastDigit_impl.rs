use vstd::prelude::*;

verus! {

spec fn factorial(n: int) -> int
    recommends n >= 0
    decreases n when n >= 0
{
    if n == 0 { 1 } else { n * factorial((n - 1) as int) }
}

// <vc-helpers>
spec fn factorial_spec(n: int) -> int
    recommends n >= 0
    decreases n when n >= 0
{
    if n == 0 { 1 } else { n * factorial_spec((n - 1) as int) }
}

proof fn factorial_spec_positive(n: int)
    requires n >= 0
    ensures factorial_spec(n) >= 1
    decreases n
{
    if n == 0 {
        assert(factorial_spec(0) == 1);
    } else {
        factorial_spec_positive(n - 1);
        assert(factorial_spec(n) == n * factorial_spec(n - 1));
        assert(factorial_spec(n) >= 1);
    }
}

proof fn factorial_spec_bounded(n: int)
    requires 0 <= n < 10
    ensures factorial_spec(n) <= 3628800
    decreases n
{
    if n == 0 {
        assert(factorial_spec(0) == 1);
    } else {
        factorial_spec_bounded(n - 1);
        assert(factorial_spec(n) == n * factorial_spec(n - 1));
    }
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
    let digit = (n % 10) as int;
    let mut result: u64 = 1;
    let mut i: int = 1;

    while i <= digit
        invariant
            0 <= i <= digit + 1,
            digit < 10,
            result == factorial_spec(i - 1),
            result <= 3628800
    {
        proof {
            factorial_spec_positive(i - 1);
            factorial_spec_bounded(digit);
        }
        result = result * (i as u64);
        i = i + 1;
    }

    proof {
        if digit == 0 {
            assert(result == 1);
            assert(factorial_spec(0) == 1);
        } else {
            assert(i == digit + 1);
            assert(result == factorial_spec(digit));
        }
    }

    result
}
// </vc-code>

fn main() {
}

}