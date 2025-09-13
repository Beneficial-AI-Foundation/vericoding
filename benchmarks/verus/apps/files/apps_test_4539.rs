// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sum_of_digits(n: int) -> int
  requires n >= 0
  decreases n
{
  if n == 0 { 0 }
  else { (n % 10) + sum_of_digits(n / 10) }
}

spec fn valid_input(n: int) -> bool {
  n >= 1
}

spec fn is_divisible_by_digit_sum(n: int) -> bool
  requires n >= 1
{
  n % sum_of_digits(n) == 0
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: String)
  requires valid_input(n)
  ensures result == "Yes" || result == "No"
  ensures result == "Yes" <==> is_divisible_by_digit_sum(n)
// </vc-spec>
// <vc-code>
{
  assume(false);
  String::new()
}
// </vc-code>


}

fn main() {}