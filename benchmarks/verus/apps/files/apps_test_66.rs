// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

verus! {
// </vc-preamble>

// <vc-helpers>
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
// </vc-helpers>

// <vc-spec>
fn solve(t: int, w: int, b: int) -> (result: (int, int))
  requires valid_input(t, w, b)
  ensures 
    valid_fraction(result.0, result.1) &&
    is_irreducible_fraction(result.0, result.1)
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}