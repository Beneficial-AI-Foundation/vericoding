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
fn compute_gcd(mut a: i8, mut b: i8) -> (result: i8)
    requires a > 0, b > 0
    ensures result as int == gcd(a as int, b as int)
{
    /* helper modified by LLM (iteration 5): fixed old() usage in invariant */
    let orig_a = a;
    let orig_b = b;
    while b != 0
        invariant
            a > 0,
            b >= 0,
            gcd(a as int, b as int) == gcd(orig_a as int, orig_b as int)
        decreases b
    {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}
// </vc-helpers>

// <vc-spec>
fn solve(r: i8, b: i8, k: i8) -> (result: String)
  requires valid_input(r as int, b as int, k as int)
  ensures result@ == (if can_avoid_consecutive(r as int, b as int, k as int) { "OBEY"@ } else { "REBEL"@ })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed arithmetic overflow by casting to larger types */
    let min_color = if r <= b { r } else { b };
    let max_color = if r <= b { b } else { r };
    
    let gcd_val = compute_gcd(min_color, max_color);
    
    // Cast to i16 to avoid overflow in arithmetic operations
    let gcd_i16 = gcd_val as i16;
    let max_color_i16 = max_color as i16;
    let min_color_i16 = min_color as i16;
    
    let max_consecutive = -((gcd_i16 - max_color_i16) / min_color_i16) as i8;
    
    if max_consecutive < k {
        "OBEY".to_string()
    } else {
        "REBEL".to_string()
    }
}
// </vc-code>


}

fn main() {}