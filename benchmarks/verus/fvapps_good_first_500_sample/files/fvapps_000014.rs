// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn can_make_square_spec(a1: u32, b1: u32, a2: u32, b2: u32) -> bool {
    /* Two rectangles can form a square if they can be arranged to create a square
       Either horizontally adjacent or vertically adjacent */
    (a1 == a2 && b1 + b2 == a1) || 
    (a1 == b2 && b1 + a2 == a1) ||
    (b1 == a2 && a1 + b2 == b1) ||
    (b1 == b2 && a1 + a2 == b1)
}

fn can_make_square(a1: u32, b1: u32, a2: u32, b2: u32) -> (result: bool)
    requires a1 > 0 && b1 > 0 && a2 > 0 && b2 > 0,
    ensures result == can_make_square_spec(a1, b1, a2, b2),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>

proof fn can_make_square_symmetric_first_rect(a1: u32, b1: u32, a2: u32, b2: u32)
    requires a1 > 0 && b1 > 0 && a2 > 0 && b2 > 0,
    ensures can_make_square_spec(a1, b1, a2, b2) == can_make_square_spec(b1, a1, a2, b2),
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn can_make_square_symmetric_second_rect(a1: u32, b1: u32, a2: u32, b2: u32)
    requires a1 > 0 && b1 > 0 && a2 > 0 && b2 > 0,
    ensures can_make_square_spec(a1, b1, a2, b2) == can_make_square_spec(a1, b1, b2, a2),
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn can_make_square_symmetric_swap_rects(a1: u32, b1: u32, a2: u32, b2: u32)
    requires a1 > 0 && b1 > 0 && a2 > 0 && b2 > 0,
    ensures can_make_square_spec(a1, b1, a2, b2) == can_make_square_spec(a2, b2, a1, b1),
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn can_make_square_identical_rects_false(n: u32)
    requires n > 0,
    ensures can_make_square_spec(n, n, n, n) == false,
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn can_make_square_known_case1()
    ensures can_make_square_spec(2, 3, 3, 1) == true,
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn can_make_square_known_case2()
    ensures can_make_square_spec(3, 2, 1, 3) == true,
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn can_make_square_known_case3()
    ensures can_make_square_spec(3, 3, 1, 3) == false,
{
    assume(false); // TODO: Remove this line and implement the proof
}

}

fn main() {}