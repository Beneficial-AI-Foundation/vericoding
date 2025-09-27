// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn MOD() -> nat { 998244353 }

fn solve_ipl_rooms(p: u32, q: u32, r: u32) -> (result: u32)
    requires p > 0 && q > 0 && r > 0,
    ensures 
        result < MOD(),
        (p + q/2 < r) ==> (result == 0),
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
    // /* Apps difficulty: interview */
    // /* Assurance level: guarded_and_plausible */

    // /* Test cases:
    //  * solve_ipl_rooms(2, 1, 4) should return 0
    //  * solve_ipl_rooms(2, 4, 4) should return 3
    //  * solve_ipl_rooms(2, 5, 4) should return 10
    //  */
}