// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_brother_numbers(a: int, b: int) -> bool {
    1 <= a <= 3 && 1 <= b <= 3 && a != b
}

spec fn late_brother(a: int, b: int) -> int
    recommends valid_brother_numbers(a, b)
{
    6 - a - b
}

spec fn is_valid_result(a: int, b: int, result: int) -> bool {
    valid_brother_numbers(a, b) ==> 
        (1 <= result <= 3 && result != a && result != b)
}
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int) -> (result: int)
    requires 
        valid_brother_numbers(a, b)
    ensures 
        is_valid_result(a, b, result) &&
        result == late_brother(a, b)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}