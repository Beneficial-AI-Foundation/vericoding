// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= 12 && 1 <= b <= 31
}

spec fn takahashi_count(a: int, b: int) -> int
    recommends valid_input(a, b)
{
    if a > b { a - 1 } else { a }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int) -> (result: int)
    requires valid_input(a, b)
    ensures 
        result == takahashi_count(a, b) &&
        (a > b ==> result == a - 1) &&
        (a <= b ==> result == a)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}