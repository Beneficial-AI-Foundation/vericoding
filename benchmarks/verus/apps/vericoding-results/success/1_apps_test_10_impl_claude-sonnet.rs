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
/* helper modified by LLM (iteration 3): added proof blocks to fix lemma verification */
proof fn lemma_min_days_off_correct(n: int)
    requires n >= 1
    ensures
        min_days_off(n) >= 0,
        min_days_off(n) <= n,
        min_days_off(n) == 2 * (n / 7) + if n % 7 > 5 { n % 7 - 5 } else { 0 },
{
}

proof fn lemma_max_days_off_correct(n: int)
    requires n >= 1
    ensures
        max_days_off(n) >= 0,
        max_days_off(n) <= n,
        max_days_off(n) == 2 * (n / 7) + if n % 7 < 2 { n % 7 } else { 2 },
{
}

proof fn lemma_min_max_relationship(n: int)
    requires n >= 1
    ensures min_days_off(n) <= max_days_off(n)
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<i8>)
  requires valid_input(n as int)
  ensures valid_output(result@.map(|i: int, x: i8| x as int), n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): preserved implementation from previous version */
    let complete_weeks = n / 7;
    let remaining_days = n % 7;
    
    let min_additional = if remaining_days > 5 {
        remaining_days - 5
    } else {
        0
    };
    
    let max_additional = if remaining_days < 2 {
        remaining_days
    } else {
        2
    };
    
    let min_result = 2 * complete_weeks + min_additional;
    let max_result = 2 * complete_weeks + max_additional;
    
    proof {
        lemma_min_days_off_correct(n as int);
        lemma_max_days_off_correct(n as int);
        lemma_min_max_relationship(n as int);
    }
    
    let mut result = Vec::new();
    result.push(min_result);
    result.push(max_result);
    
    result
}
// </vc-code>


}

fn main() {}