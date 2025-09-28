// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    -100 <= a <= 100 && -100 <= b <= 100 && (a + b) % 2 == 0 && (a - b) % 2 == 0
}

spec fn correct_solution(a: int, b: int, x: int, y: int) -> bool {
    a == x + y && b == x - y
}
// </vc-preamble>

// <vc-helpers>
proof fn solution_exists(a: int, b: int)
    requires
        valid_input(a, b),
    ensures
        exists|x: int, y: int| correct_solution(a, b, x, y)
{
    let x = (a + b) / 2;
    let y = (a - b) / 2;
    assert(x + y == a);
    assert(x - y == b);
    assert(correct_solution(a, b, x, y));
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: (i8, i8))
    requires valid_input(a as int, b as int)
    ensures correct_solution(a as int, b as int, result.0 as int, result.1 as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added bounds checking to prevent overflow */
    proof {
        solution_exists(a as int, b as int);
    }
    assert(-100 <= a as int <= 100);
    assert(-100 <= b as int <= 100);
    let x = ((a as i16) + (b as i16)) / 2;
    let y = ((a as i16) - (b as i16)) / 2;
    proof {
        assert(correct_solution(a as int, b as int, x as int, y as int));
    }
    (x as i8, y as i8)
}
// </vc-code>


}

fn main() {}