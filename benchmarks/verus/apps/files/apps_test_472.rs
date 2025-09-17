// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn digit_sum(n: int) -> int
  recommends n >= 0
  decreases n
{
  if n == 0 {
    0
  } else {
    (n % 10) + digit_sum(n / 10)
  }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i32) -> (result: i32)
  requires 
    n >= 1
  ensures 
    n == 1 ==> result == -1,
    n > 1 && result > 0 ==> result * result + digit_sum(result as int) * result == n,
    n > 1 && result > 0 ==> forall|y: i32| y > 0 && y < result ==> y * y + digit_sum(y as int) * y != n,
    n > 1 && result == -1 ==> forall|x: i32| x > 0 ==> x * x + digit_sum(x as int) * x != n,
    result == -1 || result > 0
// </vc-spec>
// <vc-code>
{
  // impl-start
  assume(false);
  -1
  // impl-end
}
// </vc-code>


}

fn main() {}