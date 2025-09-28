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
/* helper modified by LLM (iteration 5): Removed as no helpers are needed. */
// </vc-helpers>

// <vc-spec>
fn solve(x1: i8, y1: i8, x2: i8, y2: i8) -> (result: Vec<i8>)
    requires valid_input(x1 as int, y1 as int, x2 as int, y2 as int)
    ensures valid_output(x1 as int, y1 as int, x2 as int, y2 as int, result@.map(|i, v: i8| v as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Moved to using ghost locals for intermediate int values to satisfy compilation. */
{
    let ghost x1_int = x1 as int;
    let ghost y1_int = y1 as int;
    let ghost x2_int = x2 as int;
    let ghost y2_int = y2 as int;

    let ghost (x3_val, y3_val) = compute_third_vertex(x1_int, y1_int, x2_int, y2_int);
    let ghost (x4_val, y4_val) = compute_fourth_vertex(x1_int, y1_int, x2_int, y2_int);

    let mut result = Vec::new();
    result.push(x3_val as i8);
    result.push(y3_val as i8);
    result.push(x4_val as i8);
    result.push(y4_val as i8);
    result
}
// </vc-code>


}

fn main() {}