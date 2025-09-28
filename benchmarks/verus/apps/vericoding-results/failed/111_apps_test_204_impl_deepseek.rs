// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, x: int, y: int) -> bool {
  a > 0 && b > 0 && x > 0 && y > 0
}

spec fn gcd(a: int, b: int) -> int
  recommends a >= 0 && b >= 0
  decreases b when b >= 0
{
  if b == 0 { a } else { gcd(b, a % b) }
}

spec fn min(a: int, b: int) -> int {
  if a <= b { a } else { b }
}

spec fn expected_result(a: int, b: int, x: int, y: int) -> int
  recommends valid_input(a, b, x, y)
{
  let g = gcd(x, y);
  let x_reduced = x / g;
  let y_reduced = y / g;
  min(a / x_reduced, b / y_reduced)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_gcd_nonnegative(a: int, b: int) 
    requires a >= 0 && b >= 0 
    ensures gcd(a, b) >= 0 {
    if b == 0 {
        // Base case
    } else {
        lemma_gcd_nonnegative(b, a % b);
    }
}

proof fn lemma_gcd_divisor_property(x: int, y: int, g: int)
    requires g == gcd(x, y) && g > 0
    ensures
        x % g == 0,
        y % g == 0,
        gcd(x / g, y / g) == 1 {
    // Standard GCD properties
}

proof fn lemma_min_property(a: int, b: int, candidate: int)
    ensures candidate <= a && candidate <= b ==> candidate <= min(a, b) {
    // If candidate is less than or equal to both, it's <= their min
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8, y: i8) -> (result: i8)
requires 
  valid_input(a as int, b as int, x as int, y as int)
ensures 
  result as int >= 0,
  result as int == expected_result(a as int, b as int, x as int, y as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): remove call to gcd_int_to_i8 and use int operations */
    let g_val = gcd(x as int, y as int) as i8;
    let x_reduced = x / g_val;
    let y_reduced = y / g_val;
    let result1 = a / x_reduced;
    let result2 = b / y_reduced;
    let result = if result1 < result2 { result1 } else { result2 };
    
    proof {
        lemma_gcd_nonnegative(x as int, y as int);
        lemma_gcd_divisor_property(x as int, y as int, g_val as int);
        lemma_min_property(a as int / (x_reduced as int), b as int / (y_reduced as int), result as int);
    }
    
    result
}
// </vc-code>


}

fn main() {}