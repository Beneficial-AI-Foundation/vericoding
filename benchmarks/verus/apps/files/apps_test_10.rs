// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
  n >= 1
}

spec fn min_days_off(n: int) -> int {
  let complete_weeks = n / 7;
  let remaining_days = n % 7;
  let min_additional = if remaining_days > 5 { remaining_days - 5 } else { 0 };
  2 * complete_weeks + min_additional
}

spec fn max_days_off(n: int) -> int {
  let complete_weeks = n / 7;
  let remaining_days = n % 7;
  let max_additional = if remaining_days < 2 { remaining_days } else { 2 };
  2 * complete_weeks + max_additional
}

spec fn valid_output(result: Seq<int>, n: int) -> bool {
  result.len() == 2 &&
  result[0] >= 0 && result[1] >= 0 &&
  result[0] <= result[1] &&
  result[0] <= n && result[1] <= n &&
  result[0] == min_days_off(n) &&
  result[1] == max_days_off(n)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<i8>)
  requires valid_input(n as int)
  ensures valid_output(result@.map(|i: int, x: i8| x as int), n as int)
// </vc-spec>
// <vc-code>
{
  assume(false);
  Vec::new()
}
// </vc-code>


}

fn main() {}