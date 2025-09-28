// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int, a: int) -> bool {
    0 <= x <= 9 && 0 <= a <= 9
}

spec fn correct_output(x: int, a: int, result: int) -> bool {
    result == (if x < a { 0nat as int } else { 10nat as int })
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_less_than_implies_zero(x: int, a: int)
    requires
        valid_input(x, a),
        x < a,
    ensures correct_output(x, a, 0)
{
}

proof fn lemma_greater_equal_implies_ten(x: int, a: int)
    requires
        valid_input(x, a),
        x >= a,
    ensures correct_output(x, a, 10)
{
}

// </vc-helpers>

// <vc-spec>
fn solve(x: i8, a: i8) -> (result: i8)
    requires valid_input(x as int, a as int)
    ensures correct_output(x as int, a as int, result as int)
// </vc-spec>
// <vc-code>
{
    proof {
        if x < a {
            lemma_less_than_implies_zero(x as int, a as int);
        } else {
            lemma_greater_equal_implies_ten(x as int, a as int);
        }
    }
    let result = if x < a { 0 } else { 10 };
    result
}
// </vc-code>


}

fn main() {}