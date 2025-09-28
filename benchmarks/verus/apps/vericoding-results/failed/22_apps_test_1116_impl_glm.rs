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
/* helper modified by LLM (iteration 5): fix arithmetic underflow/overflow and postcondition */
fn gcd_exec(a: i32, b: i32) -> (result: i32)
    requires a > 0 && b >= 0
    ensures result == gcd(a as int, b as int)
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd_exec(b, a % b)
    }
}

/* helper modified by LLM (iteration 5): fix arithmetic underflow/overflow and postcondition */
fn max_consecutive_same_color_exec(r: i32, b: i32) -> (result: i32)
    requires r > 0 && b > 0
    ensures result == max_consecutive_same_color(r as int, b as int)
{
    let a = if r <= b { r } else { b };
    let b_val = if r <= b { b } else { r };
    let n = gcd_exec(a, b_val);
    let diff = b_val - n;
    let result = -diff / a;
    result
}

/* helper modified by LLM (iteration 5): change parameters from int to i32 */
fn can_avoid_consecutive_exec(r: i32, b: i32, k: i32) -> (result: bool)
    requires r > 0 && b > 0 && k > 0
    ensures result == can_avoid_consecutive(r as int, b as int, k as int)
{
    let m = max_consecutive_same_color_exec(r, b);
    m < k
}
// </vc-helpers>

// <vc-spec>
fn solve(r: i8, b: i8, k: i8) -> (result: String)
  requires valid_input(r as int, b as int, k as int)
  ensures result@ == (if can_avoid_consecutive(r as int, b as int, k as int) { "OBEY"@ } else { "REBEL"@ })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): keep previous implementation as it was correct */
{
    let r_i32 = r as i32;
    let b_i32 = b as i32;
    let k_i32 = k as i32;
    if can_avoid_consecutive_exec(r_i32, b_i32, k_i32) {
        "OBEY".to_string()
    } else {
        "REBEL".to_string()
    }
}
// </vc-code>


}

fn main() {}