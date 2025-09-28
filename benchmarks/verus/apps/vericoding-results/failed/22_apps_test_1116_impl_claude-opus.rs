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
/* helper modified by LLM (iteration 5): Added lemma to prove GCD step preserves value */
proof fn lemma_gcd_step(a: int, b: int)
    requires a > 0, b >= 0
    ensures gcd(a, b) == gcd(b, a % b)
{
    // Follows from the definition of gcd
}
// </vc-helpers>

// <vc-spec>
fn solve(r: i8, b: i8, k: i8) -> (result: String)
  requires valid_input(r as int, b as int, k as int)
  ensures result@ == (if can_avoid_consecutive(r as int, b as int, k as int) { "OBEY"@ } else { "REBEL"@ })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed GCD loop to maintain invariant and compute correct result */
    let a = if r <= b { r } else { b };
    let b_val = if r <= b { b } else { r };
    
    let mut n = a;
    let mut m = b_val;
    
    while m != 0
        invariant
            n > 0,
            m >= 0,
            gcd(a as int, b_val as int) == gcd(n as int, m as int)
        decreases m
    {
        proof {
            lemma_gcd_step(n as int, m as int);
        }
        let temp = m;
        m = n % m;
        n = temp;
    }
    
    // n now contains gcd(a, b_val)
    let max_consec = -((n - b_val) / a);
    
    if max_consec < k {
        "OBEY".to_string()
    } else {
        "REBEL".to_string()
    }
}
// </vc-code>


}

fn main() {}