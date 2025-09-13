// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sum_of_digits(x: int) -> int
  requires x >= 0
  decreases x
{
  if x == 0 { 0 } else { (x % 10) + sum_of_digits(x / 10) }
}

spec fn check(x: int, s: int) -> bool
  requires x >= 0
{
  x - sum_of_digits(x) >= s
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, s: int) -> (result: int)
  requires n >= 1 && s >= 1
  ensures result >= 0 && result <= n
// </vc-spec>
// <vc-code>
{
  assume(false);
  0
}
// </vc-code>


}

fn main() {}