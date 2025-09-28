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

// </vc-helpers>

// <vc-spec>
fn solve(x1: i8, y1: i8, x2: i8, y2: i8) -> (result: Vec<i8>)
    requires valid_input(x1 as int, y1 as int, x2 as int, y2 as int)
    ensures valid_output(x1 as int, y1 as int, x2 as int, y2 as int, result@.map(|i, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed truncate attribute syntax with parentheses */
    let x1_i32 = x1 as i32;
    let y1_i32 = y1 as i32;
    let x2_i32 = x2 as i32;
    let y2_i32 = y2 as i32;

    let dx = x2_i32 - x1_i32;
    let dy = y2_i32 - y1_i32;
    
    let x3 = x2_i32 - dy;
    let y3 = y2_i32 + dx;
    let x4 = x1_i32 - dy;
    let y4 = y1_i32 + dx;

    proof {
        let (x3_spec, y3_spec) = compute_third_vertex(x1 as int, y1 as int, x2 as int, y2 as int);
        let (x4_spec, y4_spec) = compute_fourth_vertex(x1 as int, y1 as int, x2 as int, y2 as int);
        
        // Convert our computed i32 values to int for comparison
        let x3_int = x3 as int;
        let y3_int = y3 as int;
        let x4_int = x4 as int;
        let y4_int = y4 as int;
        
        assert(x3_int == x3_spec);
        assert(y3_int == y3_spec);
        assert(x4_int == x4_spec);
        assert(y4_int == y4_spec);
    }

    vec![
        (#[verifier::truncate] x3 as i8),
        (#[verifier::truncate] y3 as i8),
        (#[verifier::truncate] x4 as i8),
        (#[verifier::truncate] y4 as i8),
    ]
}
// </vc-code>


}

fn main() {}