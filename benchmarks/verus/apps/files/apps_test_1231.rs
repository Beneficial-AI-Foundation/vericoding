// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: int, b: int) -> bool {
    0 <= a <= 100 && 0 <= b <= 100
}

spec fn valid_output(result: &str) -> bool {
    result == "YES" || result == "NO"
}

spec fn interval_exists(a: int, b: int) -> bool {
    abs_spec(a - b) <= 1 && a + b > 0
}

spec fn abs_spec(x: int) -> int {
    if x >= 0 { x } else { -x }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int) -> (result: String)
    requires 
        valid_input(a, b)
    ensures 
        valid_output(&result),
        (result == "YES") <==> interval_exists(a, b)
// </vc-spec>
// <vc-code>
{
    assume(false);
    String::new()
}
// </vc-code>


}

fn main() {}