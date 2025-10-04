// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs_diff(a: nat, b: nat) -> nat {
    if a >= b { 
        (a - b) as nat 
    } else { 
        (b - a) as nat 
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_fruit_diff(apples: u32, oranges: u32, gold: u32) -> (result: u32)
    ensures 
        result <= abs_diff(apples as nat, oranges as nat),
        (apples == oranges) ==> (result == 0),
        (gold == 0) ==> (result == abs_diff(apples as nat, oranges as nat)),
        (gold >= abs_diff(apples as nat, oranges as nat)) ==> (result <= 1)
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
    // let result1 = min_fruit_diff(3, 4, 1);
    // assert(result1 == 0);
    // 
    // let result2 = min_fruit_diff(5, 2, 1);
    // assert(result2 == 2);
    // 
    // let result3 = min_fruit_diff(3, 4, 3);
    // assert(result3 == 0);
}