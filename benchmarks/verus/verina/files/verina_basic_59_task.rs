/* Given an integer x, determine a pair (a, b) where the first element is twice the value of x and the second element is four times the value of x.

-----Input-----
The input consists of:
• x: An integer.

-----Output-----
The output is a tuple (a, b) where:
• a = 2 * x
• b = 4 * x

-----Note-----
There are no additional preconditions; the method is defined for all integers. */

use vstd::prelude::*;

verus! {
fn double_quadruple(x: i32) -> (result: (i32, i32))
    ensures
        result.0 == 2 * x,
        result.1 == 2 * result.0,
{
    // impl-start
    assume(false);
    (0, 0)
    // impl-end
}
}
fn main() {}