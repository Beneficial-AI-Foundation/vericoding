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
fn min_days_off_calc(n: i8) -> (min_days: i8)
    requires
        n >= 1,
    ensures
        min_days >= 0,
        min_days as int == min_days_off(n as int),
{
    let complete_weeks = n / 7;
    let remaining_days = n % 7;
    let min_additional = if remaining_days > 5 { remaining_days - 5 } else { 0 };
    2 * complete_weeks + min_additional
}

fn max_days_off_calc(n: i8) -> (max_days: i8)
    requires
        n >= 1,
    ensures
        max_days >= 0,
        max_days as int == max_days_off(n as int),
{
    let complete_weeks = n / 7;
    let remaining_days = n % 7;
    let max_additional = if remaining_days < 2 { remaining_days } else { 2 };
    2 * complete_weeks + max_additional
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<i8>)
  requires valid_input(n as int)
  ensures valid_output(result@.map(|i: int, x: i8| x as int), n as int)
// </vc-spec>
// <vc-code>
{
    let min_days = min_days_off_calc(n);
    let max_days = max_days_off_calc(n);
    let mut result = Vec::new();
    result.push(min_days);
    result.push(max_days);
    result
}
// </vc-code>


}

fn main() {}