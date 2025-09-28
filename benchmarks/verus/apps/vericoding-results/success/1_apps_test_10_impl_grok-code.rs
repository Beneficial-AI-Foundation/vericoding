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
/* code modified by LLM (iteration 3): compute min and max days off using executable logic matching the spec functions */
    proof {
        let n_int = n as int;
        let complete_weeks = n_int / 7;
        let remaining_days = n_int % 7;
        let min_additional = if remaining_days > 5 { remaining_days - 5 } else { 0 };
        let max_additional = if remaining_days < 2 { remaining_days } else { 2 };
        let min_days = (2 * complete_weeks + min_additional);
        let max_days = (2 * complete_weeks + max_additional);
        assert(min_days == min_days_off(n_int));
        assert(max_days == max_days_off(n_int));
    }
    let complete_weeks_i8 = n / 7;
    let remaining_days_i8 = n % 7;
    let min_additional_i8 = if remaining_days_i8 > 5 { remaining_days_i8 - 5 } else { 0 };
    let max_additional_i8 = if remaining_days_i8 < 2 { remaining_days_i8 } else { 2 };
    let min_days_i8 = 2 * complete_weeks_i8 + min_additional_i8;
    let max_days_i8 = 2 * complete_weeks_i8 + max_additional_i8;
    let mut result = Vec::new();
    result.push(min_days_i8);
    result.push(max_days_i8);
    result
}
// </vc-code>


}

fn main() {}