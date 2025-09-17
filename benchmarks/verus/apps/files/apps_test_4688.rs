// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn power(base: int, exp: int) -> int
  decreases exp when exp >= 0
{
  if exp <= 0 { 1 } else { base * power(base, exp - 1) }
}

spec fn valid_input(n: int, k: int) -> bool
{
  1 <= n <= 1000 && 2 <= k <= 1000
}

spec fn painting_ways(n: int, k: int) -> int
{
  if valid_input(n, k) { k * power(k - 1, n - 1) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, k: int) -> (result: int)
  requires 
    valid_input(n, k)
  ensures 
    result == painting_ways(n, k),
    result > 0
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