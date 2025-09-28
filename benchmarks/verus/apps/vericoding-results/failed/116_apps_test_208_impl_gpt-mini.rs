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
/* helper modified by LLM (iteration 5): int_abs nonnegativity lemma */
proof fn lemma_int_abs_nonneg(x: int)
    ensures
        int_abs(x) >= 0,
{
    if x >= 0 {
        assert(int_abs(x) == x);
        assert(x >= 0);
    } else {
        assert(int_abs(x) == -x);
        assert(-x >= 0);
    }
}

/* helper modified by LLM (iteration 5): bounds on coordinate differences under valid_input */
proof fn lemma_diff_bounds(x1: int, y1: int, x2: int, y2: int)
    requires
        valid_input(x1, y1, x2, y2),
    ensures
        int_abs(x2 - x1) <= 200,
{
    assert(-100 <= x1 && x1 <= 100);
    assert(-100 <= x2 && x2 <= 100);
    if x2 >= x1 {
        assert(x2 - x1 <= 200);
        assert(int_abs(x2 - x1) == x2 - x1);
    } else {
        assert(x1 - x2 <= 200);
        assert(int_abs(x2 - x1) == x1 - x2);
    }
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
    /* code modified by LLM (iteration 5): use i32 for arithmetic to avoid spec 'int' in runtime, compute differences and build Vec<i8> */
    let xi1_i32: i32 = x1 as i32;
    let yi1_i32: i32 = y1 as i32;
    let xi2_i32: i32 = x2 as i32;
    let yi2_i32: i32 = y2 as i32;

    let dx: i32 = if xi2_i32 >= xi1_i32 { xi2_i32 - xi1_i32 } else { xi1_i32 - xi2_i32 };
    let dy: i32 = if yi2_i32 >= yi1_i32 { yi2_i32 - yi1_i32 } else { yi1_i32 - yi2_i32 };

    if xi1_i32 != xi2_i32 && yi1_i32 != yi2_i32 && dx != dy {
        let mut res: Vec<i8> = Vec::new();
        res.push(-1i8);
        res
    } else if xi1_i32 != xi2_i32 && yi1_i32 != yi2_i32 && dx == dy {
        let mut res: Vec<i8> = Vec::new();
        res.push(x1);
        res.push(y2);
        res.push(x2);
        res.push(y1);
        res
    } else if xi1_i32 == xi2_i32 {
        let add: i32 = if yi2_i32 >= yi1_i32 { yi2_i32 - yi1_i32 } else { yi1_i32 - yi2_i32 };
        let a_i8: i8 = #[verifier::truncate] ((xi1_i32 + add) as i8);
        let mut res: Vec<i8> = Vec::new();
        res.push(a_i8);
        res.push(y1);
        res.push(a_i8);
        res.push(y2);
        res
    } else {
        let add: i32 = if xi2_i32 >= xi1_i32 { xi2_i32 - xi1_i32 } else { xi1_i32 - xi2_i32 };
        let b_i8: i8 = #[verifier::truncate] ((yi1_i32 + add) as i8);
        let mut res: Vec<i8> = Vec::new();
        res.push(x1);
        res.push(b_i8);
        res.push(x2);
        res.push(b_i8);
        res
    }
}

// </vc-code>


}

fn main() {}