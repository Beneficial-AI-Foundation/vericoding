/* This task requires writing a Verus method of which given a number n and divisor d, it counts all the number that is smaller than
n whose sum of digits is divisible by d.
-----Input-----
The input consists of two usize:
n: usize
d: usize where d > 0

-----Output-----
The output is a natural number:
Ensure this match the count that satisfy the property. */

use vstd::prelude::*;

verus! {
spec fn sum_of_digits(x: nat) -> nat
    decreases x
{
    if x == 0 { 0 } else { (x % 10) + sum_of_digits(x / 10) }
}

spec fn is_sum_divisible_by(x: nat, d: nat) -> bool
{
    (sum_of_digits(x) % d) == 0
}
fn count_sum_divisible_by(n: usize, d: usize) -> (result: usize)
    requires d > 0,
    ensures 
        result <= n,
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}
fn main() {}