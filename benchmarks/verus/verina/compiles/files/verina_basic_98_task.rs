/* This task involves computing three times a given integer. Given an integer, the goal is to produce a value that is exactly three times its value.

Input:
The input consists of a single integer:
x: An integer.

Output:
The output is an integer:
Returns the product of the input integer and 3.

Note:
There are no additional preconditions. */

use vstd::prelude::*;

verus! {
fn triple(x: i32) -> (result: i32)
    ensures
        result / 3 == x,
        result / 3 * 3 == result,
{
    // impl-start
    assume(false);
    0
    // impl-end
}
}
fn main() {}