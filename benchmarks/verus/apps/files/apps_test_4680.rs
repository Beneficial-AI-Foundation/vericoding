// <vc-preamble>
use vstd::prelude::*;

verus! {
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: &'static str)
    requires 
        valid_input(a as int, b as int, c as int),
    ensures 
        valid_output(result),
        (result == "YES") <==> can_form_haiku(a as int, b as int, c as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}