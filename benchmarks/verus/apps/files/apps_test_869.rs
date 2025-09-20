// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int) -> bool
{
  a >= 1 && b >= 1
}

spec fn max_different_days(a: int, b: int) -> int
{
  if a < b { a } else { b }
}

spec fn remaining_after_different(a: int, b: int) -> int
{
  if a > b { a - max_different_days(a, b) } else { b - max_different_days(a, b) }
}

spec fn same_days(a: int, b: int) -> int
{
  remaining_after_different(a, b) / 2
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: (i8, i8))
  requires valid_input(a as int, b as int)
  ensures ({
      let (days_different, days_same) = result;
      days_different as int == max_different_days(a as int, b as int) &&
      days_same as int == same_days(a as int, b as int) &&
      days_different >= 0 &&
      days_same >= 0 &&
      days_different <= a && days_different <= b
  })
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}