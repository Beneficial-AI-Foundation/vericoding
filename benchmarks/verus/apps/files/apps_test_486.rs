// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn product_of_digits(x: int) -> int
  recommends x >= 0
{
  if x == 0 { 1 }
  else if x < 10 { x }
  else { (x % 10) * product_of_digits(x / 10) }
}

spec fn max_product_of_digits_in_range(n: int) -> int
  recommends n >= 1
{
  if n == 1 { 1 }
  else {
    let current = product_of_digits(n);
    let rest = max_product_of_digits_in_range(n - 1);
    if current > rest { current } else { rest }
  }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: int)
  requires 
    n >= 1
  ensures 
    result == max_product_of_digits_in_range(n),
    result >= 1,
    forall|k: int| 1 <= k <= n ==> product_of_digits(k) <= result,
    exists|k: int| 1 <= k <= n && product_of_digits(k) == result
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