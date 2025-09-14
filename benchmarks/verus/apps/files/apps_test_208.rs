// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn valid_input(x1: int, y1: int, x2: int, y2: int) -> bool {
    -100 <= x1 <= 100 && -100 <= y1 <= 100 && -100 <= x2 <= 100 && -100 <= y2 <= 100
}

spec fn is_invalid_case(x1: int, y1: int, x2: int, y2: int) -> bool {
    x1 != x2 && y1 != y2 && abs(x1 - x2) != abs(y1 - y2)
}

spec fn is_diagonal_case(x1: int, y1: int, x2: int, y2: int) -> bool {
    x1 != x2 && y1 != y2 && abs(x1 - x2) == abs(y1 - y2)
}

spec fn is_vertical_edge_case(x1: int, y1: int, x2: int, y2: int) -> bool {
    x1 == x2
}

spec fn is_horizontal_edge_case(x1: int, y1: int, x2: int, y2: int) -> bool {
    x1 != x2 && y1 == y2
}

spec fn expected_diagonal_result(x1: int, y1: int, x2: int, y2: int) -> Seq<int> {
    seq![x1, y2, x2, y1]
}

spec fn expected_vertical_result(x1: int, y1: int, x2: int, y2: int) -> Seq<int> {
    seq![x1 + abs(y2 - y1), y1, x1 + abs(y2 - y1), y2]
}

spec fn expected_horizontal_result(x1: int, y1: int, x2: int, y2: int) -> Seq<int> {
    seq![x1, y1 + abs(x2 - x1), x2, y1 + abs(x2 - x1)]
}

spec fn valid_output(result: Seq<int>) -> bool {
    (result.len() == 1 && result[0] == -1) ||
    (result.len() == 4 && (forall|i: int| 0 <= i < 4 ==> -1000 <= result[i] <= 1000))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(x1: int, y1: int, x2: int, y2: int) -> (result: Vec<int>)
    requires valid_input(x1, y1, x2, y2)
    ensures 
        valid_output(result@),
        is_invalid_case(x1, y1, x2, y2) ==> result@ == seq![-1],
        is_diagonal_case(x1, y1, x2, y2) ==> result@ == expected_diagonal_result(x1, y1, x2, y2),
        is_vertical_edge_case(x1, y1, x2, y2) ==> result@ == expected_vertical_result(x1, y1, x2, y2),
        is_horizontal_edge_case(x1, y1, x2, y2) ==> result@ == expected_horizontal_result(x1, y1, x2, y2)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}

fn main() {}