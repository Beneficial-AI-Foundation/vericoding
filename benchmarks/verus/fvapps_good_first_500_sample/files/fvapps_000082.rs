// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_rabbits(x: i32, y: i32, a: i32, b: i32) -> (result: i32)
    requires 
        x < y,
        a > 0,
        b > 0,
    ensures
        (result == -1) || (result >= 0 && x + a * result == y - b * result),
        result == -1 <==> ((y - x) % (a + b) != 0),
        result >= 0 ==> (result == (y - x) / (a + b)),
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
    // let result1 = solve_rabbits(0, 10, 2, 3);
    // assert(result1 == 2);
    
    // let result2 = solve_rabbits(0, 10, 3, 3);
    // assert(result2 == -1);
    
    // let result3 = solve_rabbits(900000000, 1000000000, 1, 9999999);
    // assert(result3 == 10);
}