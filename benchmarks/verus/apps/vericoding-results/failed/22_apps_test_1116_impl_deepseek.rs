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

proof fn gcd_lemma(a: int, b: int, d: int)
    requires
        a > 0,
        b == 0 || (b > 0 && a % b >= 0),  // Fix: Ensure modulo is non-negative
        d == gcd(a, b),
    ensures
        d > 0,
        a % d == 0,
        b % d == 0
  decreases b when a > 0 && b >= 0
{
    if b > 0 {
        gcd_lemma(b, a % b, d);
    }
}

proof fn commute_gcd(a: int, b: int)
    ensures gcd(a, b) == gcd(b, a)
{
    if a > 0 && b >= 0 {
        let d1 = gcd(a, b);
        let d2 = gcd(b, a);
        gcd_lemma(a, b, d1);
        gcd_lemma(b, a, d2);
        assert(d1 == d2);
    } else if b > 0 && a >= 0 {
        let d1 = gcd(b, a);
        let d2 = gcd(a, b);
        gcd_lemma(b, a, d1);
        gcd_lemma(a, b, d2);
        assert(d1 == d2);
    } else {
        // Handle remaining cases
        assert(gcd(a, b) == gcd(b, a));
    }
}

/* helper modified by LLM (iteration 5): Fixed gcd_exec with proper termination and modulo handling */
fn gcd_exec(a: i8, b: i8) -> (result: i8)
    requires a > 0 && b >= 0
    ensures result as int == gcd(a as int, b as int)
    decreases b as int
{
    if b == 0 {
        a
    } else {
        let remainder = a % b;
        gcd_exec(b, if remainder >= 0 { remainder } else { remainder + b })
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(r: i8, b: i8, k: i8) -> (result: String)
  requires valid_input(r as int, b as int, k as int)
  ensures result@ == (if can_avoid_consecutive(r as int, b as int, k as int) { "OBEY"@ } else { "REBEL"@ })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed calculation to match specification */
    let (a_val, b_val) = if r <= b { (r, b) } else { (b, r) };
    let n = gcd_exec(a_val, b_val);
    
    // Calculate max consecutive same color using integer arithmetic with proper casting
    let n_int = n as i16;
    let b_int = b_val as i16;
    let a_int = a_val as i16;
    
    let numerator = n_int - b_int;
    let divided = numerator / a_int;
    let max_consecutive = (-divided) as i8;
    
    if max_consecutive < k {
        "OBEY".to_string()
    } else {
        "REBEL".to_string()
    }
}
// </vc-code>


}

fn main() {}