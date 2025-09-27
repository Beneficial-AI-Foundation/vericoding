// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_min_chocolate_break_cost(n: nat, m: nat, k: nat) -> (result: nat)
    requires 
        n > 0,
        m > 0,
        k <= 25,
    ensures 
        (n * m == k) ==> (result == 0),
        (k == 0) ==> (result == 0),
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
    // let result1 = find_min_chocolate_break_cost(2, 2, 1);
    // assert(result1 == 5);
    
    // let result2 = find_min_chocolate_break_cost(2, 2, 3);
    // assert(result2 == 5);
    
    // let result3 = find_min_chocolate_break_cost(2, 2, 4);
    // assert(result3 == 0);
}