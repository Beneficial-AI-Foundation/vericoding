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
proof fn algebra_lemma(a: int, b: int)
    requires
        valid_input(a, b),
    ensures
        correct_solution(a, b, (a + b) / 2, (a - b) / 2),
{
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: (i8, i8))
    requires valid_input(a as int, b as int)
    ensures correct_solution(a as int, b as int, result.0 as int, result.1 as int)
// </vc-spec>
// <vc-code>
{
    proof {
        algebra_lemma(a as int, b as int);
    }

    let x = ((a as i16 + b as i16) / 2) as i8;
    let y = ((a as i16 - b as i16) / 2) as i8;

    (x, y)
}
// </vc-code>


}

fn main() {}