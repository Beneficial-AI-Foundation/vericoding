// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, x: int, a: int, b: int) -> bool {
    2 <= n <= 100 && 0 <= x <= 100 && 1 <= a <= n && 1 <= b <= n && a != b
}

spec fn max_distance(n: int, x: int, a: int, b: int) -> int
    recommends valid_input(n, x, a, b)
{
    let initial_distance = if a >= b { a - b } else { b - a };
    let max_possible_distance = initial_distance + x;
    let max_line_distance = n - 1;
    if max_possible_distance <= max_line_distance { max_possible_distance } else { max_line_distance }
}

spec fn valid_result(n: int, x: int, a: int, b: int, result: int) -> bool
    recommends valid_input(n, x, a, b)
{
    result == max_distance(n, x, a, b) && 0 <= result <= n - 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed types from int to i8 and used i16 for intermediate calculations */
fn calculate_max_dist(n: i8, x: i8, a: i8, b: i8) -> (result: i8)
    requires
        valid_input(n as int, x as int, a as int, b as int),
    ensures
        valid_result(n as int, x as int, a as int, b as int, result as int),
{
    let initial_distance = if a >= b { a - b } else { b - a };

    // Use a wider type for intermediate calculation to prevent overflow
    let max_possible_distance = (initial_distance as i16) + (x as i16);
    let max_line_distance = (n as i16) - 1;
    
    let result_i16 = if max_possible_distance <= max_line_distance {
        max_possible_distance
    } else {
        max_line_distance
    };

    result_i16 as i8
}
// </vc-helpers>

// <vc-spec>
fn solve_rival_distance(n: i8, x: i8, a: i8, b: i8) -> (result: i8)
    requires
        valid_input(n as int, x as int, a as int, b as int),
    ensures
        valid_result(n as int, x as int, a as int, b as int, result as int),
        result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): call the fixed executable helper function */
    calculate_max_dist(n, x, a, b)
}
// </vc-code>


}

fn main() {}