// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(d: int, t: int, s: int) -> bool {
    1 <= d <= 10000 && 1 <= t <= 10000 && 1 <= s <= 10000
}

spec fn can_travel(d: int, t: int, s: int) -> bool {
    d <= t * s
}
// </vc-helpers>

// <vc-spec>
fn solve(d: int, t: int, s: int) -> (result: &'static str)
    requires 
        valid_input(d, t, s),
    ensures 
        can_travel(d, t, s) ==> result == "Yes",
        !can_travel(d, t, s) ==> result == "No",
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}