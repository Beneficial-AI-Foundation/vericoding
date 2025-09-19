// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn num_teams(rating: Vec<i32>) -> (result: usize)
    ensures 
        result >= 0,
        rating.len() < 3 ==> result == 0,
        (forall|x: i32, y: i32| #[trigger] rating@.contains(x) && #[trigger] rating@.contains(y) ==> x == y) ==> result == 0,
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
fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // println!("{}", num_teams(vec![2, 5, 3, 4, 1])); // Expected: 3
    // println!("{}", num_teams(vec![2, 1, 3])); // Expected: 0  
    // println!("{}", num_teams(vec![1, 2, 3, 4])); // Expected: 4
}