// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100
}

spec fn is_triangle(a: int, b: int, c: int) -> bool {
    a + b > c && a + c > b && b + c > a
}

spec fn min_operations_needed(a: int, b: int, c: int) -> int
    recommends valid_input(a, b, c)
{
    let max_val = if a >= b && a >= c { a } else if b >= c { b } else { c };
    let sum_of_other_two = a + b + c - max_val;
    if max_val - sum_of_other_two + 1 > 0 { max_val - sum_of_other_two + 1 } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int)
    ensures 
        result >= 0,
        result as int == min_operations_needed(a as int, b as int, c as int),
        (result as int == 0) <==> is_triangle(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}