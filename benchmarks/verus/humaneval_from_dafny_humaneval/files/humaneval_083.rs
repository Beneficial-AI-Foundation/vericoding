// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
  n >= 1
}

spec fn power(base: int, exp: int) -> int
  decreases exp when exp >= 0
{
  if exp <= 0 { 1 } else { base * power(base, exp - 1) }
}

spec fn count_starts_with_1(n: int) -> int {
  power(10, n - 1)
}

spec fn count_ends_with_1(n: int) -> int {
  if n == 1 { 1 } else { 9 * power(10, n - 2) }
}

spec fn count_starts_and_ends_with_1(n: int) -> int {
  if n <= 2 { 1 } else { power(10, n - 2) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn starts_one_ends(n: int) -> (result: int)
  requires 
    valid_input(n)
  ensures 
    result == count_starts_with_1(n) + count_ends_with_1(n) - count_starts_and_ends_with_1(n),
    result >= 0
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}