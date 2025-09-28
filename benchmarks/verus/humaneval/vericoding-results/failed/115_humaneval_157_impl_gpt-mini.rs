// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): valid_triangle spec using int */
spec fn valid_triangle(a: int, b: int, c: int) -> bool {
    a > 0 && b > 0 && c > 0 &&
    a + b > c && a + c > b && b + c > a
}

/* helper modified by LLM (iteration 5): is_right_triangle spec using int */
spec fn is_right_triangle(a: int, b: int, c: int) -> bool {
    a * a + b * b == c * c || 
    a * a + c * c == b * b || 
    b * b + c * c == a * a
}

/* helper modified by LLM (iteration 5): valid_right_triangle spec combining predicates */
spec fn valid_right_triangle(a: int, b: int, c: int) -> bool {
    valid_triangle(a, b, c) && is_right_triangle(a, b, c)
}
// </vc-helpers>

// <vc-spec>
fn right_angle_triangle(a: i8, b: i8, c: i8) -> (result: bool)
    ensures result <==> valid_right_triangle(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute using mathematical int to avoid machine-integer overflow and prove equivalence */
    let ai: int = a as int;
    let bi: int = b as int;
    let ci: int = c as int;

    let valid: bool = ai > 0 && bi > 0 && ci > 0 &&
        ai + bi > ci && ai + ci > bi && bi + ci > ai;

    let right: bool = ai * ai + bi * bi == ci * ci ||
        ai * ai + ci * ci == bi * bi ||
        bi * bi + ci * ci == ai * ai;

    let res: bool = valid && right;

    proof {
        assert(res == valid_right_triangle(ai, bi, ci));
    }

    res
}
// </vc-code>


}

fn main() {}