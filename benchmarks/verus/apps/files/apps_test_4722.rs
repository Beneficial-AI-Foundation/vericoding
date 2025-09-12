// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100
}

spec fn distribution_possible(a: int, b: int) -> bool {
    a % 3 == 0 || b % 3 == 0 || (a + b) % 3 == 0
}
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int) -> (result: String)
    requires 
        valid_input(a, b)
    ensures 
        result@ == new_strlit("Possible").view() <==> distribution_possible(a, b),
        result@ == new_strlit("Possible").view() || result@ == new_strlit("Impossible").view()
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}