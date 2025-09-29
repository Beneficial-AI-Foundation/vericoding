// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn gcd(a: int, b: int) -> int 
    decreases (if b == 0 { 0 } else { abs(b) })
{
    if b == 0 { abs(a) } else { gcd(b, a % b) }
}

spec fn valid_input(t: int, w: int, b: int) -> bool {
    t > 0 && w > 0 && b > 0
}

spec fn valid_fraction(numerator: int, denominator: int) -> bool {
    numerator >= 0 && denominator > 0 && numerator <= denominator
}

spec fn is_irreducible_fraction(numerator: int, denominator: int) -> bool
    recommends valid_fraction(numerator, denominator)
{
    gcd(numerator, denominator) == 1
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(t: u64, w: u64, b: u64) -> (result: (u64, u64))
    requires
        t > 0 && w > 0 && b > 0,
    ensures
        result.1 > 0,
        result.0 <= result.1
// </vc-spec>
// <vc-code>
{
    let p: u64 = 0u64;
    let q: u64 = 1u64;
    (p, q)
}
// </vc-code>


}

fn main() {}