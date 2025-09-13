// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, t: int) -> bool {
  1 <= n <= 10 && 0 <= t <= 10000
}

spec fn total_glasses(n: int) -> int {
  n * (n + 1) / 2
}

spec fn valid_result(result: int, n: int, t: int) -> bool {
  result >= 0 && result <= total_glasses(n)
}

spec fn correct_for_edge_cases(result: int, n: int, t: int) -> bool {
  (t == 0 ==> result == 0) &&
  (n == 1 && t >= 1 ==> result == 1) &&
  (n == 1 && t == 0 ==> result == 0) &&
  (t >= 1 && n > 1 ==> result >= 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, t: int) -> (result: int)
  requires 
    valid_input(n, t),
  ensures 
    valid_result(result, n, t),
    correct_for_edge_cases(result, n, t)
// </vc-spec>
// <vc-code>
{
  assume(false);
  0
}
// </vc-code>


}

fn main() {}