// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(k: int, a: int, b: int) -> bool {
  k > 0 && a <= b
}

spec fn floor_div(a: int, b: int) -> int {
  if a >= 0 { a / b }
  else { (a - b + 1) / b }
}

spec fn count_divisibles_in_range(k: int, a: int, b: int) -> int {
  floor_div(b, k) - floor_div(a - 1, k)
}
// </vc-helpers>

// <vc-spec>
fn solve(k: int, a: int, b: int) -> (result: int)
  requires
    valid_input(k, a, b),
  ensures
    result >= 0,
    result == count_divisibles_in_range(k, a, b),
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}