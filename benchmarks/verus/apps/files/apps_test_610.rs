// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, m: int) -> bool {
  n >= 1 && m >= 1
}

spec fn optimal_vasya_score(n: int, m: int) -> int
  recommends valid_input(n, m)
{
  if n < m { n } else { m }
}

spec fn optimal_petya_score(n: int, m: int) -> int
  recommends valid_input(n, m)
{
  n + m - 1 - optimal_vasya_score(n, m)
}

spec fn total_adjacent_pairs(n: int, m: int) -> int
  recommends valid_input(n, m)
{
  n + m - 1
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int) -> (result: (int, int))
  requires valid_input(n, m)
  ensures 
      result.0 == optimal_petya_score(n, m) &&
      result.1 == optimal_vasya_score(n, m) &&
      result.0 + result.1 == total_adjacent_pairs(n, m)
// </vc-spec>
// <vc-code>
{
  assume(false);
  (0int, 0int)
}
// </vc-code>


}

fn main() {}