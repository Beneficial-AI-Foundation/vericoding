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
/* helper modified by LLM (iteration 5): added decreases clause */
proof fn lemma_gcd_divides(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures (a % gcd(a, b) == 0) && (b % gcd(a, b) == 0)
    decreases b
{
    if b == 0 {
        assert(gcd(a,0) == a);
        assert(a % a == 0);
    } else {
        let g = gcd(b, a % b);
        lemma_gcd_divides(b, a % b);
        let q = a / b;
        let r = a % b;
        assert(a == q * b + r);
        assert(b % g == 0);
        assert(r % g == 0);
        assert((q * b) % g == 0);
        assert((q * b + r) % g == 0);
    }
}

fn exec_gcd(a: i8, b: i8) -> (result: i8)
  requires a > 0 && b > 0
  ensures 
    result == gcd(a as int, b as int) as i8,
    result > 0,
    (a as int) % (result as int) == 0,
    (b as int) % (result as int) == 0,
{
    let mut x = a;
    let mut y = b;
    while y != 0
        invariant 
            x > 0 && y >= 0,
            gcd(x as int, y as int) == gcd(a as int, b as int),
        decreases y
    {
        let temp = y;
        y = x % y;
        x = temp;
    }
    proof {
        lemma_gcd_divides(a as int, b as int);
    }
    x
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
/* code modified by LLM (iteration 4): removed ghost code from exec mode */
{
    let g = exec_gcd(x, y);
    let x_reduced = x / g;
    let y_reduced = y / g;
    proof {
        assert(g > 0);
        assert(x > 0);
        assert(y > 0);
        assert(x >= g);
        assert(y >= g);
        assert(x_reduced >= 1);
        assert(y_reduced >= 1);
    }
    let candidate1 = a / x_reduced;
    let candidate2 = b / y_reduced;
    if candidate1 <= candidate2 {
        candidate1
    } else {
        candidate2
    }
}
// </vc-code>


}

fn main() {}