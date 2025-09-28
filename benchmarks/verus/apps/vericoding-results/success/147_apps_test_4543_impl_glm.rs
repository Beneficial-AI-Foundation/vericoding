// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {

spec fn is_perfect_square(n: int) -> bool
  recommends n >= 0
{
  exists|sqrt_n: int| sqrt_n >= 0 && #[trigger] (sqrt_n * sqrt_n) == n
}
/* Helper functions for string/int conversion - these would need implementation */
fn int_to_string(n: int) -> (result: String)
  requires n >= 0
  ensures result@.len() > 0
{
  assume(false);
  unreached()
}

fn string_to_int(s: String) -> (result: int)
  requires s@.len() > 0
  ensures result >= 0
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): changed from int to i32 for non-ghost computation */
fn is_sum_perfect_square(a: i8, b: i8) -> bool
  requires a as int >= 1 && a as int <= 100,
           b as int >= 1 && b as int <= 100
{
  let sum = a as i32 + b as i32;
  sum == 4 ||
  sum == 9 ||
  sum == 16 ||
  sum == 25 ||
  sum == 36 ||
  sum == 49 ||
  sum == 64 ||
  sum == 81 ||
  sum == 100 ||
  sum == 121 ||
  sum == 144 ||
  sum == 169 ||
  sum == 196
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: String)
  requires a as int >= 1 && a as int <= 100,
           b as int >= 1 && b as int <= 100
  ensures result@ == "Yes"@ || result@ == "No"@
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed string return type conversion */
{
  if is_sum_perfect_square(a, b) {
    return "Yes".to_string();
  } else {
    return "No".to_string();
  }
}
// </vc-code>


}

fn main() {}