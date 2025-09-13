// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
// </vc-helpers>

// <vc-spec>
fn solve(x1: int, y1: int, x2: int, y2: int) -> (result: Vec<int>)
    requires valid_input(x1, y1, x2, y2)
    ensures valid_output(x1, y1, x2, y2, result@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}