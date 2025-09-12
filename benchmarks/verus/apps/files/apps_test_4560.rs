// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, a: int) -> bool {
    1 <= n <= 10000 && 0 <= a <= 1000
}

spec fn can_pay_exactly(n: int, a: int) -> bool {
    n % 500 <= a
}

spec fn valid_output(result: &str) -> bool {
    result == "Yes" || result == "No"
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, a: int) -> (result: String)
    requires 
        valid_input(n, a)
    ensures 
        valid_output(&result) && 
        ((result == "Yes") <==> can_pay_exactly(n, a))
// </vc-spec>
// <vc-code>
{
    assume(false);
    String::new()
}
// </vc-code>


}

fn main() {}