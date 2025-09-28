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
/* helper modified by LLM (iteration 3): min_days_off definition */
proof fn min_days_off_def(n: int)
    requires
        n >= 1,
    ensures
        min_days_off(n) == {
            let complete_weeks = n / 7;
            let remaining_days = n % 7;
            let min_additional = if remaining_days > 5 { remaining_days - 5 } else { 0 };
            2 * complete_weeks + min_additional
        },
{
    assert(min_days_off(n) == {
        let complete_weeks = n / 7;
        let remaining_days = n % 7;
        let min_additional = if remaining_days > 5 { remaining_days - 5 } else { 0 };
        2 * complete_weeks + min_additional
    });
}

/* helper modified by LLM (iteration 3): max_days_off definition */
proof fn max_days_off_def(n: int)
    requires
        n >= 1,
    ensures
        max_days_off(n) == {
            let complete_weeks = n / 7;
            let remaining_days = n % 7;
            let max_additional = if remaining_days < 2 { remaining_days } else { 2 };
            2 * complete_weeks + max_additional
        },
{
    assert(max_days_off(n) == {
        let complete_weeks = n / 7;
        let remaining_days = n % 7;
        let max_additional = if remaining_days < 2 { remaining_days } else { 2 };
        2 * complete_weeks + max_additional
    });
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<i8>)
  requires valid_input(n as int)
  ensures valid_output(result@.map(|i: int, x: i8| x as int), n as int)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute min/max using i8 arithmetic and invoke proof lemmas */
  let complete_weeks = n / 7_i8;
  let remaining_days = n % 7_i8;
  let min_additional = if remaining_days > 5_i8 { remaining_days - 5_i8 } else { 0_i8 };
  let max_additional = if remaining_days < 2_i8 { remaining_days } else { 2_i8 };
  let min_val = 2_i8 * complete_weeks + min_additional;
  let max_val = 2_i8 * complete_weeks + max_additional;
  proof {
    let n_int: int = n as int;
    min_days_off_def(n_int);
    max_days_off_def(n_int);
    assert(min_days_off(n_int) == (min_val as int));
    assert(max_days_off(n_int) == (max_val as int));
  }
  let mut result = Vec::new();
  result.push(min_val);
  result.push(max_val);
  result
}

// </vc-code>


}

fn main() {}