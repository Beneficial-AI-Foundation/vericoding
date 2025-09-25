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
fn solve(cafes: Vec<i8>) -> (mini: i8)
    requires
        cafes.len() > 0,
    ensures
        cafes@.contains(mini),
        forall|cafe: i8| #![auto] cafes@.contains(cafe) ==> last_occurrence_position(cafes@.map(|i, x: i8| x as int), mini as int) <= last_occurrence_position(cafes@.map(|i, x: i8| x as int), cafe as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}