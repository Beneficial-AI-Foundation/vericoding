// <vc-preamble>
use vstd::prelude::*;

verus! {
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error in ensures clause by adding comma. */
fn safe_floor_div(numerator: i8, denominator: i8) -> (result: i8)
    requires
        denominator != 0,
    ensures
        (denominator as int > 0 && numerator as int >= 0) ==> (result as int == numerator as int / denominator as int),
        (denominator as int > 0 && numerator as int < 0) ==> (result as int == ((numerator as int - denominator as int + 1) / denominator as int)),
        (denominator as int < 0 && numerator as int >= 0) ==> (result as int == ((numerator as int - denominator as int - 1) / denominator as int)),
        (denominator as int < 0 && numerator as int < 0) ==> (result as int == numerator as int / denominator as int),
{
    if numerator >= 0 && denominator > 0 {
        numerator / denominator
    } else if numerator < 0 && denominator > 0 {
        (numerator - denominator + 1) / denominator
    } else if numerator >= 0 && denominator < 0 {
        (numerator - denominator - 1) / denominator
    } else {
        numerator / denominator
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(k: i8, a: i8, b: i8) -> (result: i8)
  requires
    valid_input(k as int, a as int, b as int),
  ensures
    result >= 0,
    result as int == count_divisibles_in_range(k as int, a as int, b as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No changes needed in the code block itself, it was correct. */
{
    let count_b = safe_floor_div(b, k);
    let a_minus_1 = a - 1;
    let count_a_minus_1 = safe_floor_div(a_minus_1, k);
    (count_b - count_a_minus_1) as i8
}
// </vc-code>


}

fn main() {}