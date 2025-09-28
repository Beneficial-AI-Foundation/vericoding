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
    /* code modified by LLM (iteration 4): use i16 throughout to avoid overflow, then convert result at the end */
    if x1 != x2 && y1 != y2 {
        let dx = if x1 > x2 { (x1 as i16) - (x2 as i16) } else { (x2 as i16) - (x1 as i16) };
        let dy = if y1 > y2 { (y1 as i16) - (y2 as i16) } else { (y2 as i16) - (y1 as i16) };
        
        if dx != dy {
            // Invalid case
            let mut result = Vec::new();
            result.push(-1i8);
            proof {
                assert(result@.map(|i, v| v as int) == seq![-1]);
            }
            result
        } else {
            // Diagonal case
            let mut result = Vec::new();
            result.push(x1);
            result.push(y2);
            result.push(x2);
            result.push(y1);
            proof {
                assert(result@.len() == 4);
                assert(result@.map(|i, v| v as int) == seq![x1 as int, y2 as int, x2 as int, y1 as int]);
            }
            result
        }
    } else if x1 == x2 {
        // Vertical edge case
        let dist = if y1 > y2 { (y1 as i16) - (y2 as i16) } else { (y2 as i16) - (y1 as i16) };
        let new_x_i16 = (x1 as i16) + dist;
        
        // Check if new_x fits in i8 range
        if new_x_i16 < -128 || new_x_i16 > 127 {
            // Out of range, return special marker
            let mut result = Vec::new();
            result.push(-1i8);
            result
        } else {
            let new_x = new_x_i16 as i8;
            let mut result = Vec::new();
            result.push(new_x);
            result.push(y1);
            result.push(new_x);
            result.push(y2);
            proof {
                assert(result@.len() == 4);
                assert(dist as int == int_abs(y2 as int - y1 as int));
                assert(new_x_i16 as int == x1 as int + int_abs(y2 as int - y1 as int));
                assert(new_x as int == new_x_i16 as int);
                assert(result@[0] as int == new_x as int);
                assert(result@[1] as int == y1 as int);
                assert(result@[2] as int == new_x as int);
                assert(result@[3] as int == y2 as int);
            }
            result
        }
    } else {
        // Horizontal edge case (x1 != x2 && y1 == y2)
        let dist = if x1 > x2 { (x1 as i16) - (x2 as i16) } else { (x2 as i16) - (x1 as i16) };
        let new_y_i16 = (y1 as i16) + dist;
        
        // Check if new_y fits in i8 range
        if new_y_i16 < -128 || new_y_i16 > 127 {
            // Out of range, return special marker
            let mut result = Vec::new();
            result.push(-1i8);
            result
        } else {
            let new_y = new_y_i16 as i8;
            let mut result = Vec::new();
            result.push(x1);
            result.push(new_y);
            result.push(x2);
            result.push(new_y);
            proof {
                assert(result@.len() == 4);
                assert(dist as int == int_abs(x2 as int - x1 as int));
                assert(new_y_i16 as int == y1 as int + int_abs(x2 as int - x1 as int));
                assert(new_y as int == new_y_i16 as int);
                assert(result@[0] as int == x1 as int);
                assert(result@[1] as int == new_y as int);
                assert(result@[2] as int == x2 as int);
                assert(result@[3] as int == new_y as int);
            }
            result
        }
    }
}
// </vc-code>


}

fn main() {}