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
// </vc-helpers>

// <vc-spec>
fn solve(n: int, s: int) -> (result: int)
requires n >= 1 && s >= 1
ensures result >= 0 && result <= n
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}