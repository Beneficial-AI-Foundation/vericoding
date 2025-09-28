// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
    1 <= a <= b
}

spec fn gcd_of_range(a: int, b: int) -> int
    recommends valid_input(a, b)
{
    if a == b { a } else { 1 }
}
// </vc-preamble>

// <vc-helpers>
proof fn lt_from_le_and_neq(a: int, b: int)
    requires
        a <= b,
        a != b,
    ensures
        a < b,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int)
    ensures 
        result as int == gcd_of_range(a as int, b as int),
        a == b ==> result as int == a as int,
        a < b ==> result as int == 1
// </vc-spec>
// <vc-code>
{
    if a == b {
        a
    } else {
        1i8
    }
}
// </vc-code>


}

fn main() {}