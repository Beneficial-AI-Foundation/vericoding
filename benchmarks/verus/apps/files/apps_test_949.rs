// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= b
}

spec fn gcd_of_range(a: int, b: int) -> int
    recommends valid_input(a, b)
{
    if a == b { a } else { 1 }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int) -> (result: int)
    requires 
        valid_input(a, b)
    ensures 
        result == gcd_of_range(a, b),
        a == b ==> result == a,
        a < b ==> result == 1
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}