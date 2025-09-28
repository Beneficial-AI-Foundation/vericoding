// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int, y: int) -> bool {
    -100 <= x <= 100 && -100 <= y <= 100
}

spec fn is_origin_or_first_point(x: int, y: int) -> bool {
    (x == 0 && y == 0) || (x == 1 && y == 0)
}

spec fn is_right_edge(x: int, y: int) -> bool {
    x >= 1 && -x + 1 < y <= x
}

spec fn is_left_edge(x: int, y: int) -> bool {
    x < 0 && x <= y < -x
}

spec fn is_top_edge(x: int, y: int) -> bool {
    y > 0 && -y <= x < y
}

spec fn compute_turns(x: int, y: int) -> int
    recommends valid_input(x, y)
{
    if is_origin_or_first_point(x, y) { 
        0
    } else if is_right_edge(x, y) { 
        1 + 4 * (x - 1)
    } else if is_left_edge(x, y) { 
        3 + 4 * (-x - 1)
    } else if is_top_edge(x, y) { 
        2 + 4 * (y - 1)
    } else { 
        -4 * y
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added exec helpers for runtime checks */
fn lemma_compute_turns_cases(x: int, y: int)
    requires valid_input(x, y)
    ensures
        is_origin_or_first_point(x, y) || is_right_edge(x, y) || is_left_edge(x, y) || is_top_edge(x, y) || (!is_origin_or_first_point(x, y) && !is_right_edge(x, y) && !is_left_edge(x, y) && !is_top_edge(x, y))
{
}

fn lemma_compute_turns_non_negative(x: int, y: int)
    requires valid_input(x, y)
    ensures compute_turns(x, y) >= 0
{
    if is_origin_or_first_point(x, y) {
        assert(compute_turns(x, y) == 0);
    } else if is_right_edge(x, y) {
        assert(x >= 1);
        assert(compute_turns(x, y) == 1 + 4 * (x - 1));
        assert(4 * (x - 1) >= 0);
    } else if is_left_edge(x, y) {
        assert(x < 0);
        assert(compute_turns(x, y) == 3 + 4 * (-x - 1));
        assert(-x >= 1);
        assert(4 * (-x - 1) >= 0);
    } else if is_top_edge(x, y) {
        assert(y > 0);
        assert(compute_turns(x, y) == 2 + 4 * (y - 1));
        assert(4 * (y - 1) >= 0);
    } else {
        assert(compute_turns(x, y) == -4 * y);
        assert(y <= 0);
        assert(-4 * y >= 0);
    }
}

exec fn is_origin_or_first_point_exec(x: i8, y: i8) -> (result: bool)
    ensures result == is_origin_or_first_point(x as int, y as int)
{
    (x == 0 && y == 0) || (x == 1 && y == 0)
}

exec fn is_right_edge_exec(x: i8, y: i8) -> (result: bool)
    ensures result == is_right_edge(x as int, y as int)
{
    x >= 1 && -x + 1 < y && y <= x
}

exec fn is_left_edge_exec(x: i8, y: i8) -> (result: bool)
    ensures result == is_left_edge(x as int, y as int)
{
    x < 0 && x <= y && y < -x
}

exec fn is_top_edge_exec(x: i8, y: i8) -> (result: bool)
    ensures result == is_top_edge(x as int, y as int)
{
    y > 0 && -y <= x && x < y
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8, y: i8) -> (result: i8)
    requires 
        valid_input(x as int, y as int)
    ensures 
        result as int >= 0,
        result as int == compute_turns(x as int, y as int),
        is_origin_or_first_point(x as int, y as int) ==> result as int == 0,
        is_right_edge(x as int, y as int) ==> result as int == 1 + 4 * (x as int - 1),
        is_left_edge(x as int, y as int) ==> result as int == 3 + 4 * (-(x as int) - 1),
        is_top_edge(x as int, y as int) ==> result as int == 2 + 4 * (y as int - 1),
        !(is_origin_or_first_point(x as int, y as int) || is_right_edge(x as int, y as int) || is_left_edge(x as int, y as int) || is_top_edge(x as int, y as int)) ==> result as int == -4 * y as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using exec helpers instead of spec functions */
    proof {
        lemma_compute_turns_cases(x as int, y as int);
        lemma_compute_turns_non_negative(x as int, y as int);
    }
    
    if is_origin_or_first_point_exec(x, y) {
        0
    } else if is_right_edge_exec(x, y) {
        let turns = 1 + 4 * (x - 1);
        turns
    } else if is_left_edge_exec(x, y) {
        let turns = 3 + 4 * (-x - 1);
        turns
    } else if is_top_edge_exec(x, y) {
        let turns = 2 + 4 * (y - 1);
        turns
    } else {
        let turns = -4 * y;
        turns
    }
}
// </vc-code>


}

fn main() {}