use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Factorial(n: int) -> int
    decreases n
{
    if n <= 0 {
        1
    } else {
        n * Factorial(n - 1)
    }
}

fn FactorialOfLastDigit(n: int) -> (fact: int)
    requires
        n >= 0
    ensures
        fact == Factorial(n % 10)
{
    let last_digit = n % 10;
    
    // Since n >= 0, we know that 0 <= last_digit <= 9
    // We can compute factorial directly for these small values
    let result = if last_digit == 0 {
        1
    } else if last_digit == 1 {
        1
    } else if last_digit == 2 {
        2
    } else if last_digit == 3 {
        6
    } else if last_digit == 4 {
        24
    } else if last_digit == 5 {
        120
    } else if last_digit == 6 {
        720
    } else if last_digit == 7 {
        5040
    } else if last_digit == 8 {
        40320
    } else { // last_digit == 9
        362880
    };
    
    // Proof that our computed values match the spec
    assert(last_digit >= 0 && last_digit <= 9);
    assert(result == Factorial(last_digit)) by {
        if last_digit == 0 {
            assert(Factorial(0) == 1);
        } else if last_digit == 1 {
            assert(Factorial(1) == 1 * Factorial(0) == 1 * 1 == 1);
        } else if last_digit == 2 {
            assert(Factorial(2) == 2 * Factorial(1) == 2 * 1 == 2);
        } else if last_digit == 3 {
            assert(Factorial(3) == 3 * Factorial(2) == 3 * 2 == 6);
        } else if last_digit == 4 {
            assert(Factorial(4) == 4 * Factorial(3) == 4 * 6 == 24);
        } else if last_digit == 5 {
            assert(Factorial(5) == 5 * Factorial(4) == 5 * 24 == 120);
        } else if last_digit == 6 {
            assert(Factorial(6) == 6 * Factorial(5) == 6 * 120 == 720);
        } else if last_digit == 7 {
            assert(Factorial(7) == 7 * Factorial(6) == 7 * 720 == 5040);
        } else if last_digit == 8 {
            assert(Factorial(8) == 8 * Factorial(7) == 8 * 5040 == 40320);
        } else {
            assert(last_digit == 9);
            assert(Factorial(9) == 9 * Factorial(8) == 9 * 40320 == 362880);
        }
    };
    
    result
}

}