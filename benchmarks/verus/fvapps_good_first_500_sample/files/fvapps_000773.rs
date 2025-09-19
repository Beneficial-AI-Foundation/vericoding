// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn abs_diff(a: i32, b: i32) -> int {
    if a >= b { (a - b) as int } else { (b - a) as int }
}
// </vc-helpers>

// <vc-spec>
fn max_drone_step(n: usize, r: i32, h: Vec<i32>) -> (result: usize)
    requires 
        n > 0,
        h.len() == n,
    ensures 
        result > 0,
        forall|i: int| 0 <= i < h.len() ==> #[trigger] abs_diff(h[i], r) % (result as int) == 0,
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
    // let result1 = max_drone_step(3, 1, vec![3, 5, 11]);
    // println!("Result 1: {}", result1);
    
    // let result2 = max_drone_step(2, 4, vec![2, 8]);
    // println!("Result 2: {}", result2);
    
    // let result3 = max_drone_step(4, 5, vec![1, 3, 7, 9]);
    // println!("Result 3: {}", result3);
}