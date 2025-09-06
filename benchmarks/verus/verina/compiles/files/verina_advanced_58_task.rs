/* This task requires writing a Verus function that returns the nth "ugly number". Ugly numbers are positive integers whose only prime factors are 2, 3, or 5.

The function should generate ugly numbers in ascending order and return the nth one. The first ugly number is 1.

Input:
The input is a natural number:

n: The index (1-based) of the ugly number to return.

Output:
The output is a natural number:
The nth smallest ugly number. */

use vstd::prelude::*;

verus! {

spec fn nth_ugly_number_precond(n: nat) -> bool {
    n > 0
}
fn nth_ugly_number(n: u32) -> (result: u32)
    requires n > 0,
    ensures result > 0,
{
    // impl-start
    assume(false);
    1
    // impl-end
}
}
fn main() {}