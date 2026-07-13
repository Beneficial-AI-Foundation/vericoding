// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn solve_taxi_turns_spec(coords: Seq<(i32, i32)>) -> u8 {
    0 /* placeholder */
}

fn solve_taxi_turns(coords: Vec<(i32, i32)>) -> (result: u8)
    requires 
        coords.len() >= 3,
        coords.len() <= 50,
    ensures
        result == 0 || result == 1 || result == 2,
        result == solve_taxi_turns_spec(coords@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {}