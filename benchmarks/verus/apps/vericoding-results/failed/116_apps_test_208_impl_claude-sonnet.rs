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
/* helper modified by LLM (iteration 5): fix type casting for abs_i8 arguments */
fn abs_i8(x: i32) -> (result: i8)
    requires
        -200 <= x <= 200
    ensures
        result as int == int_abs(x as int),
        0 <= result as int <= 200
{
    if x >= 0 { x as i8 } else { (-x) as i8 }
}

proof fn lemma_abs_calculation(x1: i8, y1: i8, x2: i8, y2: i8)
    requires
        valid_input(x1 as int, y1 as int, x2 as int, y2 as int)
    ensures
        int_abs((x1 as int) - (x2 as int)) == abs_i8((x1 as i32) - (x2 as i32)) as int,
        int_abs((y1 as int) - (y2 as int)) == abs_i8((y1 as i32) - (y2 as i32)) as int
{
}

proof fn lemma_diagonal_correctness(x1: i8, y1: i8, x2: i8, y2: i8)
    requires
        valid_input(x1 as int, y1 as int, x2 as int, y2 as int),
        is_diagonal_case(x1 as int, y1 as int, x2 as int, y2 as int)
    ensures
        seq![x1 as int, y2 as int, x2 as int, y1 as int] == expected_diagonal_result(x1 as int, y1 as int, x2 as int, y2 as int)
{
}

proof fn lemma_vertical_correctness(x1: i8, y1: i8, x2: i8, y2: i8)
    requires
        valid_input(x1 as int, y1 as int, x2 as int, y2 as int),
        is_vertical_edge_case(x1 as int, y1 as int, x2 as int, y2 as int)
    ensures
        seq![(x1 + abs_i8((y2 as i32) - (y1 as i32))) as int, y1 as int, (x1 + abs_i8((y2 as i32) - (y1 as i32))) as int, y2 as int] == expected_vertical_result(x1 as int, y1 as int, x2 as int, y2 as int)
{
    lemma_abs_calculation(x1, y1, x2, y2);
}

proof fn lemma_horizontal_correctness(x1: i8, y1: i8, x2: i8, y2: i8)
    requires
        valid_input(x1 as int, y1 as int, x2 as int, y2 as int),
        is_horizontal_edge_case(x1 as int, y1 as int, x2 as int, y2 as int)
    ensures
        seq![x1 as int, (y1 + abs_i8((x2 as i32) - (x1 as i32))) as int, x2 as int, (y1 + abs_i8((x2 as i32) - (x1 as i32))) as int] == expected_horizontal_result(x1 as int, y1 as int, x2 as int, y2 as int)
{
    lemma_abs_calculation(x1, y1, x2, y2);
}
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
{
    /* code modified by LLM (iteration 5): cast i8 operands to i32 for abs_i8 calls */
    if x1 == x2 {
        // Vertical case
        let new_x = x1 + abs_i8((y2 as i32) - (y1 as i32));
        proof {
            lemma_vertical_correctness(x1, y1, x2, y2);
        }
        vec![new_x, y1, new_x, y2]
    } else if y1 == y2 {
        // Horizontal case
        let new_y = y1 + abs_i8((x2 as i32) - (x1 as i32));
        proof {
            lemma_horizontal_correctness(x1, y1, x2, y2);
        }
        vec![x1, new_y, x2, new_y]
    } else if abs_i8((x1 as i32) - (x2 as i32)) == abs_i8((y1 as i32) - (y2 as i32)) {
        // Diagonal case
        proof {
            lemma_diagonal_correctness(x1, y1, x2, y2);
        }
        vec![x1, y2, x2, y1]
    } else {
        // Invalid case
        vec![-1]
    }
}
// </vc-code>


}

fn main() {}