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
    if last_digit == 0 {
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
    }
}

}