// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn longest_consecutive_ones(xs: Seq<nat>, n: nat) -> nat {
    0
}
// </vc-helpers>

// <vc-spec>
fn max_dist_to_closest(seats: Vec<nat>) -> (result: nat)
    requires 
        seats.len() >= 2,
        seats.len() <= 20000,
        forall|i: int| 0 <= i < seats.len() ==> (seats[i] == 0 || seats[i] == 1),
        exists|i: int| 0 <= i < seats.len() && seats[i] == 1,
        exists|i: int| 0 <= i < seats.len() && seats[i] == 0,
    ensures
        result >= 0,
        result <= seats.len(),
        forall|i: int, j: int| (0 <= i < seats.len() && 0 <= j < seats.len() && 
                                i < j && seats[i] == 1 && seats[j] == 1) ==>
                               ((j - i - 1) + 1) / 2 <= result,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // let test1 = vec![1, 0, 0, 0, 1, 0, 1];
    // let result1 = max_dist_to_closest(test1);
    // println!("Test 1 result: {}", result1);

    // let test2 = vec![1, 0, 0, 0];
    // let result2 = max_dist_to_closest(test2);
    // println!("Test 2 result: {}", result2);

    // let test3 = vec![0, 1];
    // let result3 = max_dist_to_closest(test3);
    // println!("Test 3 result: {}", result3);
}