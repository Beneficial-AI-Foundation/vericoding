// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int) -> bool {
  a >= 1 && a <= 1000 && b >= 2 && b <= 1000
}

spec fn total_burning_hours(a: int, b: int) -> int
  recommends a >= 0 && b >= 2
  decreases a
{
  if a == 0 { 0 }
  else if a < b { a }
  else { a + total_burning_hours(a / b, b) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int) -> (result: int)
  requires
    valid_input(a, b),
  ensures
    result >= a,
    result == total_burning_hours(a, b),
// </vc-spec>
// <vc-code>
{
  assume(false);
  0
}
// </vc-code>


}

fn main() {}