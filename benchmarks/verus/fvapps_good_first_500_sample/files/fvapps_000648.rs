// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_latest_bus(n: usize, d: usize, buses: Vec<usize>) -> (result: usize)
    requires 
        n > 0,
        d > 0,
        buses.len() == n,
        forall|i: int| 0 <= i < buses.len() ==> buses[i] > 0 && buses[i] <= d,
    ensures 
        result <= d,
        result > 0,
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
    // let result1 = solve_latest_bus(3, 10, vec![3, 7, 2]);
    // println!("{}", result1); // Should print 6
    
    // let result2 = solve_latest_bus(4, 100, vec![11, 10, 5, 50]);
    // println!("{}", result2); // Should print 99
    
    // let result3 = solve_latest_bus(1, 1, vec![1]);
    // println!("{}", result3); // Should print 1
}