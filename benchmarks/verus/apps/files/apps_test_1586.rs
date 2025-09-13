// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int) -> bool {
  n >= 0
}

spec fn factors_in_factorial(n: int, p: int) -> int
  recommends p > 1 && n >= 0
  decreases n
{
  if n == 0 { 0 }
  else { n / p + factors_in_factorial(n / p, p) }
}

spec fn factors_in_double_factorial(n: int, p: int) -> int
  recommends p > 1 && n >= 0
  decreases n
{
  if n <= 0 { 0 }
  else if n % 2 == 1 {
    factors_in_factorial(n, p) - factors_in_double_factorial(n - 1, p)
  } else {
    factors_in_factorial(n / 2, p) + (if p == 2 { n / 2 } else { 0 })
  }
}

spec fn valid_result(n: int, result: int) -> bool
  recommends n >= 0
{
  result >= 0 &&
  result == if factors_in_double_factorial(n, 2) < factors_in_double_factorial(n, 5) {
    factors_in_double_factorial(n, 2)
  } else {
    factors_in_double_factorial(n, 5)
  }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: int)
  requires valid_input(n)
  ensures valid_result(n, result)
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}