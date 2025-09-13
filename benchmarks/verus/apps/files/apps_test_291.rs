// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn pow(base: int, exp: int) -> int
  recommends exp >= 0
{
  if exp == 0 { 1 }
  else if exp < 0 { 0 }
  else { base * pow(base, exp - 1) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int) -> (years: int)
  requires 
    1 <= a <= b <= 10,
  ensures 
    years >= 0,
    a * pow(3, years) > b * pow(2, years),
    years == 0 || a * pow(3, years - 1) <= b * pow(2, years - 1),
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}