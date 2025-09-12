// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= c <= 100 && 1 <= d <= 100
}

spec fn can_communicate(a: int, b: int, c: int, d: int) -> bool {
    if a - c >= 0 { a - c } else { c - a } <= d || 
    (if a - b >= 0 { a - b } else { b - a } <= d && if b - c >= 0 { b - c } else { c - b } <= d)
}
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int, c: int, d: int) -> (result: String)
    requires 
        valid_input(a, b, c, d),
    ensures 
        result@ == "Yes" <==> can_communicate(a, b, c, d),
        result@ == "Yes" || result@ == "No",
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}