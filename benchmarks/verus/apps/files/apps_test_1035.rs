// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int) -> bool {
  a > 0 && b > 0
}

spec fn gcd(a: int, b: int) -> int
  recommends a > 0 && b >= 0
  decreases b
{
  if b == 0 { a } else { gcd(b, a % b) }
}

spec fn count_distinct_prime_factors(n: int) -> int
  recommends n > 0
{
  if n == 1 { 0 } else { count_distinct_prime_factors_helper(n, 2) }
}

spec fn count_distinct_prime_factors_helper(n: int, i: int) -> int
  recommends n > 0 && i >= 2
  decreases 2*n - i when 2*n - i >= 0
{
  if i * i > n {
    if n > 1 { 1 } else { 0 }
  } else if n % i == 0 {
    1 + count_distinct_prime_factors_helper(divide_out_factor(n, i), i + 1)
  } else {
    count_distinct_prime_factors_helper(n, i + 1)
  }
}

spec fn divide_out_factor(n: int, factor: int) -> int
  recommends n > 0 && factor > 1 && n % factor == 0
  decreases n when n > 0
{
  let next = n / factor;
  if next % factor == 0 { divide_out_factor(next, factor) } else { next }
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
    valid_input(a, b)
  ensures 
    result > 0,
    correct_result(a, b, result)
// </vc-spec>
// <vc-code>
{
  // impl-start
  assume(false);
  unreached()
  // impl-end
}
// </vc-code>


}

fn main() {}