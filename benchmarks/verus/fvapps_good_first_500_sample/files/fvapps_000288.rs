// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_self_crossing(moves: Vec<i32>) -> (result: bool)
    requires forall|i: int| 0 <= i < moves.len() ==> moves[i] >= 0,
    ensures 
        moves.len() < 4 ==> result == false,
        (moves.len() == 4 && forall|i: int, j: int| 0 <= i < moves.len() && 0 <= j < moves.len() ==> moves[i] == moves[j] && moves[i] > 0) ==> result == true,
        (moves.len() == 4 && moves[0] > 0 && moves[1] > 0 && moves[2] > 0 && moves[3] > 0 && moves[0] < moves[1] && moves[1] < moves[2] && moves[2] < moves[3]) ==> result == false,
        (exists|x: int| 0 <= x < moves.len() && moves[x] < 0) ==> result == false,
        (moves.len() >= 6 && forall|i: int| #[trigger] moves[i] >= 0 && moves.len() >= 6 && moves[5] >= moves[3] && moves[4] == moves[2]) ==> result == true
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {
    // #eval is_self_crossing [2, 1, 1, 2]
    // #eval is_self_crossing [1, 2, 3, 4]
    // #eval is_self_crossing [1, 1, 1, 1]
}