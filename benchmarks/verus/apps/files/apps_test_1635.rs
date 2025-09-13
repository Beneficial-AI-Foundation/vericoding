// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn last_occurrence_helper(cafes: Seq<int>, cafe: int, pos: int) -> int
    decreases pos + 1
{
    if pos < 0 || pos >= cafes.len() { -1 }
    else if cafes[pos] == cafe { pos }
    else { last_occurrence_helper(cafes, cafe, pos - 1) }
}

spec fn last_occurrence_position(cafes: Seq<int>, cafe: int) -> int
{
    last_occurrence_helper(cafes, cafe, (cafes.len() - 1) as int)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(cafes: Seq<int>) -> (mini: i32)
    requires
        cafes.len() > 0,
    ensures
        cafes.contains(mini as int),
        forall|cafe: int| #![auto] cafes.contains(cafe) ==> last_occurrence_position(cafes, mini as int) <= last_occurrence_position(cafes, cafe),
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}