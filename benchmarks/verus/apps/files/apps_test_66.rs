// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(t: int, w: int, b: int) -> bool {
    t > 0 && w > 0 && b > 0
}

spec fn valid_fraction(numerator: int, denominator: int) -> bool {
    numerator >= 0 && denominator > 0 && numerator <= denominator
}

spec fn gcd(a: int, b: int) -> int {
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a <= b {
        gcd(a, b - a)
    } else {
        gcd(a - b, b)
    }
}

spec fn is_irreducible_fraction(numerator: int, denominator: int) -> bool {
    gcd(numerator, denominator) == 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(t: int, w: int, b: int) -> (ret: (int, int))
    requires valid_input(t, w, b)
    ensures 
        valid_fraction(ret.0, ret.1) &&
        is_irreducible_fraction(ret.0, ret.1)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}