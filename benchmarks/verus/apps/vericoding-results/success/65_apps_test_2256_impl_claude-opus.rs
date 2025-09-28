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
    /* code modified by LLM (iteration 4): Fixed syntax error by adding missing parentheses around assert argument */
    let initial_distance = if a >= b { a - b } else { b - a };
    
    proof {
        // Assert bounds on initial_distance
        assert(0 <= initial_distance as int);
        assert(initial_distance as int <= n as int - 1);
        assert((initial_distance as int) < 100);
    }
    
    // Since initial_distance < 100 and x <= 100, their sum < 200
    // But i8 max is 127, so we need to be careful
    let max_line_distance = n - 1;
    
    // Check if we can safely add
    if initial_distance <= 127 - x {
        let max_possible_distance = initial_distance + x;
        if max_possible_distance <= max_line_distance {
            max_possible_distance
        } else {
            max_line_distance
        }
    } else {
        // If adding would overflow i8, the result is definitely > n-1
        max_line_distance
    }
}
// </vc-code>


}

fn main() {}