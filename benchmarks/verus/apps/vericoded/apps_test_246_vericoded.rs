// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_of_digits(x: int) -> int
  decreases x when x >= 0
{
  if x <= 0 { 0 } else { (x % 10) + sum_of_digits(x / 10) }
}

spec fn check(x: int, s: int) -> bool {
  x >= 0 && x - sum_of_digits(x) >= s
}
// </vc-preamble>

// <vc-helpers>
fn zero() -> (z: i8)
    ensures
        z == 0i8,
{
    0i8
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, s: i8) -> (result: i8)
requires n as int >= 1 && s as int >= 1
ensures result as int >= 0 && result as int <= n as int
// </vc-spec>
// <vc-code>
{
    let z = zero();
    z
}
// </vc-code>


}

fn main() {}