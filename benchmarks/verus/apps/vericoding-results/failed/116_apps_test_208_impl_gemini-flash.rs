// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x1: int, y1: int, x2: int, y2: int) -> bool {
    -100 <= x1 <= 100 && -100 <= y1 <= 100 && -100 <= x2 <= 100 && -100 <= y2 <= 100
}

spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn is_invalid_case(x1: int, y1: int, x2: int, y2: int) -> bool {
    x1 != x2 && y1 != y2 && int_abs(x1 - x2) != int_abs(y1 - y2)
}

spec fn is_diagonal_case(x1: int, y1: int, x2: int, y2: int) -> bool {
    x1 != x2 && y1 != y2 && int_abs(x1 - x2) == int_abs(y1 - y2)
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
    seq![x1 + int_abs(y2 - y1), y1, x1 + int_abs(y2 - y1), y2]
}

spec fn expected_horizontal_result(x1: int, y1: int, x2: int, y2: int) -> Seq<int> {
    seq![x1, y1 + int_abs(x2 - x1), x2, y1 + int_abs(x2 - x1)]
}

spec fn valid_output(result: Seq<int>) -> bool {
    (result.len() == 1 && result[0] == -1) ||
    (result.len() == 4 && (forall|i: int| #![trigger result[i]] 0 <= i < 4 ==> -1000 <= result[i] <= 1000))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers. */
// </vc-helpers>

// <vc-spec>
fn solve(x1: i8, y1: i8, x2: i8, y2: i8) -> (result: Vec<i8>)
    requires 
        valid_input(x1 as int, y1 as int, x2 as int, y2 as int)
    ensures 
        valid_output(result@.map(|i, v| v as int)),
        is_invalid_case(x1 as int, y1 as int, x2 as int, y2 as int) ==> result@.map(|i, v| v as int) == seq![-1],
        is_diagonal_case(x1 as int, y1 as int, x2 as int, y2 as int) ==> result@.map(|i, v| v as int) == expected_diagonal_result(x1 as int, y1 as int, x2 as int, y2 as int),
        is_vertical_edge_case(x1 as int, y1 as int, x2 as int, y2 as int) ==> result@.map(|i, v| v as int) == expected_vertical_result(x1 as int, y1 as int, x2 as int, y2 as int),
        is_horizontal_edge_case(x1 as int, y1 as int, x2 as int, y2 as int) ==> result@.map(|i, v| v as int) == expected_horizontal_result(x1 as int, y1 as int, x2 as int, y2 as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed the types of variables from int to i8 when they are being used in exec context to avoid compilation errors. */
{
    if (x1 != x2 && y1 != y2 && vstd::math::abs(x1 - x2) != vstd::math::abs(y1 - y2)) {
        vec![-1]
    } else if (x1 != x2 && y1 != y2 && vstd::math::abs(x1 - x2) == vstd::math::abs(y1 - y2)) {
        vec![x1, y2, x2, y1]
    } else if (x1 == x2) {
        let k = vstd::math::abs(y2 - y1);
        vec![x1 + k, y1, x1 + k, y2]
    } else if (x1 != x2 && y1 == y2) {
        let k = vstd::math::abs(x2 - x1);
        vec![x1, y1 + k, x2, y1 + k]
    } else {
        assert(false);
        vec![-1]
    }
}
// </vc-code>


}

fn main() {}