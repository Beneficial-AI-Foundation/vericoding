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
/* helper modified by LLM (iteration 5): Fixed ensures syntax and return value */
proof fn lemma_requires_valid_input(x1: int, y1: int, x2: int, y2: int)
    requires valid_input(x1, y1, x2, y2)
    ensures 
        -100 <= x1 <= 100,
        -100 <= y1 <= 100,
        -100 <= x2 <= 100,
        -100 <= y2 <= 100
{
    assert(-100 <= x1);
    assert(x1 <= 100);
    assert(-100 <= y1);
    assert(y1 <= 100);
    assert(-100 <= x2);
    assert(x2 <= 100);
    assert(-100 <= y2);
    assert(y2 <= 100);
}

fn compute_third_vertex_impl(x1: i8, y1: i8, x2: i8, y2: i8) -> (i8, i8)
    ensures
        return.0 as int == compute_third_vertex(x1 as int, y1 as int, x2 as int, y2 as int).0,
        return.1 as int == compute_third_vertex(x1 as int, y1 as int, x2 as int, y2 as int).1
{
    proof {
        lemma_requires_valid_input(x1 as int, y1 as int, x2 as int, y2 as int);
    }
    (x2.wrapping_sub((y2 - y1)), y2.wrapping_add(x2 - x1))
}

fn compute_fourth_vertex_impl(x1: i8, y1: i8, x2: i8, y2: i8) -> (i8, i8)
    ensures
        return.0 as int == compute_fourth_vertex(x1 as int, y1 as int, x2 as int, y2 as int).0,
        return.1 as int == compute_fourth_vertex(x1 as int, y1 as int, x极 as int, y2 as int).1
{
    proof {
        lemma_requires_valid_input(x1 as int, y1 as int, x2 as int, y2 as极);
    }
    (x1.wrapping_sub((y2 - y1)), y1.wrapping_add(x2 - x1))
}
// </vc-helpers>

// <vc-spec>
fn solve(x1: i8, y1: i8, x2: i8, y2: i8) -> (result: Vec<i8>)
    requires valid_input(x1 as int, y1 as int, x2 as int, y2 as int)
    ensures valid_output(x1 as int, y1 as int, x2 as int, y2 as int, result@.map(|i, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed typo in variable */
    let (x3, y3) = compute_third_vertex_impl(x1, y1, x2, y2);
    let (x4, y4) = compute_fourth_vertex_impl(x1, y1, x2, y2);
    let mut result = Vec::new();
    result.push(x3);
    result.push(y3);
    result.push(x4);
    result.push(y4);
    result
}
// </vc-code>


}

fn main() {}