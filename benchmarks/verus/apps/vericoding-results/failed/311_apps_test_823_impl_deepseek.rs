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
/* helper modified by LLM (iteration 5): Fixed proof functions to use proper ghost types */
proof fn lemma_compute_turns_matches_edges(x: int, y: int)
    requires
        valid_input(x, y),
    ensures
        compute_turns(x, y) >= 0,
        is_origin_or_first_point(x, y) ==> compute_turns(x, y) == 0,
        is_right_edge(x, y) ==> compute_turns(x, y) == 1 + 4 * (x - 1),
        is_left_edge(x, y) ==> compute_turns(x, y) == 3 + 4 * (-x - 1),
        is_top_edge(x, y) ==> compute_turns(x, y) == 2 + 4 * (y - 1),
        !(is_origin_or_first_point(x, y) || is_right_edge(x, y) || is_left_edge(x, y) || is_top_edge(x, y)) ==> compute_turns(x, y) == -4 * y,
    decreases
        10 + (if x < 0 { -x } else { x } + if y < 0 { -y } else { y })
{
    reveal_with_fuel(compute_turns, 10);
}

proof fn lemma_edge_cases_mutually_exclusive(x: int, y: int)
    requires
        valid_input(x, y),
    ensures
        !(is_origin_or_first_point(x, y) && is_right_edge(x, y)),
        !(is_origin_or_first_point(x, y) && is_left_edge(x, y)),
        !(is_origin_or_first_point(x, y) && is_top_edge(x, y)),
        !(is_right_edge(x, y) && is_left_edge(x, y)),
        !(is_right_edge(x, y) && is_top_edge(x, y)),
        !(is_left_edge(x, y) && is_top_edge(x, y)),
    decreases
        5 + (if x < 0 { -x } else { x } + if y < 0 { -y } else { y })
{
    reveal_with_fuel(is_origin_or_first_point, 5);
    reveal_with_fuel(is_right_edge, 5);
    reveal_with_fuel(is_left_edge, 5);
    reveal_with_fuel(is_top_edge, 5);
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
    /* code modified by LLM (iteration 5): Fixed ghost function call by wrapping in proof block */
    proof {
        lemma_compute_turns_matches_edges(x as int, y as int);
    }
    
    if x == 0 && y == 0 {
        0
    } else if x == 1 && y == 0 {
        0
    } else if x >= 1 && -x + 1 < y && y <= x {
        (1 + 4 * (x - 1)) as i8
    } else if x < 0 && x <= y && y < -x {
        (3 + 4 * (-x - 1)) as i8
    } else if y > 0 && -y <= x && x < y {
        (2 + 4 * (y - 1)) as i8
    } else {
        (-4 * y) as i8
    }
}
// </vc-code>


}

fn main() {}