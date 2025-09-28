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
fn gcd_exec(a: i8, b: i8) -> (res: i8)
    requires
        a > 0,
        b >= 0,
    ensures
        res as int == gcd(a as int, b as int),
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd_exec(b, a % b)
    }
}

/* helper modified by LLM (iteration 2): [used i32 for intermediate calculation to correctly implement ceil division and avoid overflow] */
fn max_consecutive_same_color_exec(r: i8, b: i8) -> (res: i8)
    requires
        r > 0,
        b > 0,
    ensures
        res as int == max_consecutive_same_color(r as int, b as int),
{
    let a = if r <= b { r } else { b };
    let b_val = if r <= b { b } else { r };
    let n = gcd_exec(a, b_val);

    // The spec function calculates `ceil((b_val - n) / a)`.
    // For positive integers p, q, this is `(p + q - 1) / q` using truncating division.
    // The intermediate sum can overflow i8, so we use a larger type like i32.
    let num = b_val as i32 - n as i32 + a as i32 - 1;
    let den = a as i32;
    let res_i32 = num / den;

    // The result is provably within i8 bounds, so the cast is safe.
    res_i32 as i8
}
// </vc-helpers>

// <vc-spec>
fn solve(r: i8, b: i8, k: i8) -> (result: String)
  requires valid_input(r as int, b as int, k as int)
  ensures result@ == (if can_avoid_consecutive(r as int, b as int, k as int) { "OBEY"@ } else { "REBEL"@ })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [logic is correct assuming fixed helper] */
    let max_consecutive = max_consecutive_same_color_exec(r, b);
    if max_consecutive < k {
        String::from_str("OBEY")
    } else {
        String::from_str("REBEL")
    }
}
// </vc-code>


}

fn main() {}