/* This task requires writing a Verus method that extracts the last digit of a given non-negative integer. The method should return the last digit, which is obtained by computing the remainder when the number is divided by 10. The result must always be between 0 and 9.

-----Input-----
The input consists of a single value:
n: A non-negative integer.

-----Output-----
The output is an integer:
Returns the last digit of the input number, ensuring that the digit lies within the range 0 to 9.

-----Note-----
It is assumed that the input number n is non-negative. */

use vstd::prelude::*;

verus! {
spec fn last_digit(n: nat) -> nat
{
    // impl-start
    assume(false);
    n % 10
    // impl-end
}

proof fn last_digit_correct(n: nat)
    ensures
        last_digit(n) < 10,
        last_digit(n) == n % 10,
{
    // impl-start
    assume(false); // TODO: Remove this line and implement the proof
    // impl-end
}
}
fn main() {}