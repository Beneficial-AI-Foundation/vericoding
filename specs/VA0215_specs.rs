// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
  a > 0 && b > 0
}

spec fn gcd(a: int, b: int) -> int
  recommends a > 0 && b >= 0
  decreases b when b >= 0
{
  if b == 0 { a } else { gcd(b, a % b) }
}

spec fn count_distinct_prime_factors(n: int) -> int
  recommends n > 0
{
  if n == 1 { 0 } else { 0 }
}

spec fn count_distinct_prime_factors_helper(n: int, i: int) -> int
  recommends n > 0 && i >= 2
{
  0
}

spec fn divide_out_factor(n: int, factor: int) -> int
  recommends n > 0 && factor > 1 && n % factor == 0
{
  n / factor
}

spec fn correct_result(a: int, b: int, result: int) -> bool
  recommends a > 0 && b > 0
{
  result == count_distinct_prime_factors(gcd(a, b)) + 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int) -> (result: int)
    requires 
        valid_input(a, b),
    ensures
        result > 0,
        correct_result(a, b, result),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}