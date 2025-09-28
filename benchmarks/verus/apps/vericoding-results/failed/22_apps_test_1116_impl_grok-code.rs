// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn gcd(a: int, b: int) -> int
  decreases b when a > 0 && b >= 0
{
  if b == 0 { a } else { gcd(b, a % b) }
}

spec fn valid_input(r: int, b: int, k: int) -> bool {
  r > 0 && b > 0 && k > 0
}

spec fn max_consecutive_same_color(r: int, b: int) -> int {
  let a = if r <= b { r } else { b };
  let b_val = if r <= b { b } else { r };
  let n = gcd(a, b_val);
  -((n - b_val) / a)
}

spec fn can_avoid_consecutive(r: int, b: int, k: int) -> bool {
  valid_input(r, b, k) && max_consecutive_same_color(r, b) < k
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed trailing comma in invariant to fix compilation error */
fn gcd_exec(a: i32, b: i32) -> (result: i32)
  requires
    a > 0,
    b >= 0,
  ensures
    result as int == gcd(a as int, b as int),
{
  let mut x = a;
  let mut y = b;
  while y != 0
    invariant
      gcd(a as int, b as int) == gcd(x as int, y as int),
    decreases y when y > 0
  {
    proof {
      assert(y != 0);
    }
    let temp = x % y;
    x = y;
    y = temp;
  }
  x
}
// </vc-helpers>

// <vc-spec>
fn solve(r: i8, b: i8, k: i8) -> (result: String)
  requires valid_input(r as int, b as int, k as int)
  ensures result@ == (if can_avoid_consecutive(r as int, b as int, k as int) { "OBEY"@ } else { "REBEL"@ })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): unchanged as previous implementation is correct after fixing helpers */
{
  let r_int = r as i32;
  let b_int = b as i32;
  let k_int = k as i32;
  let a = if r_int <= b_int { r_int } else { b_int };
  let b_val = if r_int <= b_int { b_int } else { r_int };
  let n = gcd_exec(a, b_val);
  let diff = n - b_val;
  let d = diff / a;
  let rem = diff % a;
  let temp = if rem == 0 { 0 } else { rem + a };
  let div = if temp == 0 { d } else { d - 1 };
  let max_c = -div;
  let can = max_c < k_int;
  let result = if can { "OBEY".to_string() } else { "REBEL".to_string() };
  result
}
// </vc-code>


}

fn main() {}