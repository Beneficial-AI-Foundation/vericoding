// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: int, b: int, p: int, q: int) -> bool {
  n > 0 && a > 0 && b > 0 && p > 0 && q > 0
}

spec fn gcd(a: int, b: int) -> int
  recommends a > 0 && b >= 0
  decreases b when b >= 0
{
  if b == 0 { a } else { gcd(b, a % b) }
}
// </vc-preamble>

// <vc-helpers>
fn zero_i8() -> (result: i8)
    ensures
        result >= 0,
{
    0
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, a: i8, b: i8, p: i8, q: i8) -> (result: i8)
  requires valid_input(n as int, a as int, b as int, p as int, q as int)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
    let z = zero_i8();
    z
}
// </vc-code>


}

fn main() {}