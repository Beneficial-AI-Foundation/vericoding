// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 10 && 1 <= b <= 10 && 1 <= c <= 10
}

spec fn can_form_haiku(a: int, b: int, c: int) -> bool {
    (a == 5 && b == 5 && c == 7) ||
    (a == 5 && b == 7 && c == 5) ||
    (a == 7 && b == 5 && c == 5)
}

spec fn valid_output(result: &str) -> bool {
    result == "YES" || result == "NO"
}
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int, c: int) -> (result: &'static str)
    requires 
        valid_input(a, b, c),
    ensures 
        valid_output(result),
        (result == "YES") <==> can_form_haiku(a, b, c),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}