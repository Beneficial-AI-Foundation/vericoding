// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x1: int, y1: int, x2: int, y2: int) -> bool {
    (x1, y1) != (x2, y2) &&
    -100 <= x1 <= 100 && -100 <= y1 <= 100 &&
    -100 <= x2 <= 100 && -100 <= y2 <= 100
}

spec fn compute_third_vertex(x1: int, y1: int, x2: int, y2: int) -> (int, int) {
    (x2 - (y2 - y1), y2 + (x2 - x1))
}

spec fn compute_fourth_vertex(x1: int, y1: int, x2: int, y2: int) -> (int, int) {
    (x1 - (y2 - y1), y1 + (x2 - x1))
}

spec fn valid_output(x1: int, y1: int, x2: int, y2: int, result: Seq<int>) -> bool {
    result.len() == 4 &&
    result[0] == compute_third_vertex(x1, y1, x2, y2).0 &&
    result[1] == compute_third_vertex(x1, y1, x2, y2).1 &&
    result[2] == compute_fourth_vertex(x1, y1, x2, y2).0 &&
    result[3] == compute_fourth_vertex(x1, y1, x2, y2).1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed 'let...in' syntax in ensures clause */
proof fn bounds_check(x1: int, y1: int, x2: int, y2: int)
    requires
        valid_input(x1, y1, x2, y2),
    ensures
    {
        let (x3, y3) = compute_third_vertex(x1, y1, x2, y2);
        let (x4, y4) = compute_fourth_vertex(x1, y1, x2, y2);
        i8::MIN as int <= x3 && x3 <= i8::MAX as int &&
        i8::MIN as int <= y3 && y3 <= i8::MAX as int &&
        i8::MIN as int <= x4 && x4 <= i8::MAX as int &&
        i8::MIN as int <= y4 && y4 <= i8::MAX as int
    }
{
}
// </vc-helpers>

// <vc-spec>
fn solve(x1: i8, y1: i8, x2: i8, y2: i8) -> (result: Vec<i8>)
    requires valid_input(x1 as int, y1 as int, x2 as int, y2 as int)
    ensures valid_output(x1 as int, y1 as int, x2 as int, y2 as int, result@.map(|i, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use spec functions for calculations and `int` type */
    let x1_int = x1 as int;
    let y1_int = y1 as int;
    let x2_int = x2 as int;
    let y2_int = y2 as int;

    let (x3_int, y3_int) = compute_third_vertex(x1_int, y1_int, x2_int, y2_int);
    let (x4_int, y4_int) = compute_fourth_vertex(x1_int, y1_int, x2_int, y2_int);

    proof {
        bounds_check(x1_int, y1_int, x2_int, y2_int);
    }

    let x3 = x3_int as i8;
    let y3 = y3_int as i8;
    let x4 = x4_int as i8;
    let y4 = y4_int as i8;

    let mut result = Vec::with_capacity(4);
    result.push(x3);
    result.push(y3);
    result.push(x4);
    result.push(y4);
    result
}

// </vc-code>


}

fn main() {}