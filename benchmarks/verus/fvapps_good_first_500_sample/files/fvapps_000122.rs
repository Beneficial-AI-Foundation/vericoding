// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn search(list: Vec<i32>, target: i32) -> (result: bool)
    ensures result == list@.contains(target)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>

/* Apps difficulty: interview */
/* Assurance level: unguarded */

}

fn main() {
    // let result1 = search(vec![2, 5, 6, 0, 0, 1, 2], 0);
    // println!("Result 1: {}", result1); // Should be true
    
    // let result2 = search(vec![2, 5, 6, 0, 0, 1, 2], 3);
    // println!("Result 2: {}", result2); // Should be false
    
    // let result3 = search(vec![1], 1);
    // println!("Result 3: {}", result3); // Should be true
}