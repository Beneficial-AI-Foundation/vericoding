// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn max_satisfaction(satisfaction: Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        satisfaction@ == Seq::<i32>::empty() ==> result == 0,
        satisfaction@.len() == 1 && satisfaction@[0] == 0 ==> result == 0,
        satisfaction@.len() == 1 && satisfaction@[0] == 1 ==> result == 1,
        satisfaction@.len() == 1 && satisfaction@[0] == -1 ==> result == 0
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

/* Apps difficulty: interview
   Assurance level: guarded_and_plausible */

}

fn main() {
    // let result1 = max_satisfaction(vec![-1, -8, 0, 5, -9]);
    // println!("Result 1: {}", result1); // Expected: 14

    // let result2 = max_satisfaction(vec![4, 3, 2]);
    // println!("Result 2: {}", result2); // Expected: 20

    // let result3 = max_satisfaction(vec![-2, 5, -1, 0, 3, -3]);
    // println!("Result 3: {}", result3); // Expected: 35
}