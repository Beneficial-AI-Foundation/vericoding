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
/* helper modified by LLM (iteration 2): added proof keyword and body */
proof fn even_division_by_two(x: int)
    requires x % 2 == 0
    ensures (x / 2) * 2 == x
{
    assert((x / 2) * 2 == x);
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: (i8, i8))
    requires valid_input(a as int, b as int)
    ensures correct_solution(a as int, b as int, result.0 as int, result.1 as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed lemma call and added proof */
    let a_i16 = a as i16;
    let b_i16 = b as i16;
    let x_i16 = (a_i16 + b_i16) / 2;
    let y_i16 = (a_i16 - b_i16) / 2;

    proof {
        even_division_by_two(a as int + b as int);
        even_division_by_two(a as int - b as int);
        assert(x_i16 * 2 == a_i16 + b_i16);
        assert(y_i16 * 2 == a_i16 - b_i16);
        assert(-100 <= x_i16 <= 100);
        assert(-100 <= y_i16 <= 100);
    }

    let x = x_i16 as i8;
    let y = y_i16 as i8;

    return (x, y);
}
// </vc-code>


}

fn main() {}