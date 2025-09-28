// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int) -> bool {
  a >= 1 && b > a && b < 499500
}

spec fn valid_snow_depth(a: int, b: int, depth: int) -> bool {
  depth >= 1 &&
  ((b - a) * (b - a) - (a + b)) >= 2 &&
  ((b - a) * (b - a) - (a + b)) % 2 == 0
}

spec fn snow_depth_formula(a: int, b: int) -> int
  recommends valid_input(a, b) && valid_snow_depth(a, b, ((b - a) * (b - a) - (a + b)) / 2)
{
  ((b - a) * (b - a) - (a + b)) / 2
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
  requires valid_input(a as int, b as int) && valid_snow_depth(a as int, b as int, ((b as int - a as int) * (b as int - a as int) - (a as int + b as int)) / 2)
  ensures result as int >= 1 && result as int == snow_depth_formula(a as int, b as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use i32 for intermediate calculations to avoid int type in non-ghost code */
{
  let a_i32 = a as i32;
  let b_i32 = b as i32;
  let d = b_i32 - a_i32;
  let d_squared = d * d;
  let a_plus_b = a_i32 + b_i32;
  let numerator = d_squared - a_plus_b;
  let depth_i32 = numerator / 2;
  let result = depth_i32 as i8;
  result
}
// </vc-code>


}

fn main() {}