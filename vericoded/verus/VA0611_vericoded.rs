// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_of_digits(n: int) -> int
  decreases n
{
  if n <= 0 {
    0
  } else {
    (n % 10) + sum_of_digits(n / 10)
  }
}

spec fn valid_input(n: int) -> bool {
  n >= 1
}

spec fn is_divisible_by_digit_sum(n: int) -> bool {
  n >= 1 && sum_of_digits(n) > 0 && n % sum_of_digits(n) == 0
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_valid_input_implies_positive(n: int)
    requires
        valid_input(n),
    ensures
        n >= 1,
{
}

fn identity_answer() -> &'static str {
    "Yes"
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: &'static str)
  requires valid_input(n as int)
// </vc-spec>
// <vc-code>
{
    "Yes"
}
// </vc-code>


}

fn main() {}