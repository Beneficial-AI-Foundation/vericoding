// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, b: Seq<int>) -> bool {
  n >= 2 && b.len() == n - 1 && forall|i: int| 0 <= i < b.len() ==> b[i] >= 0
}

spec fn sum_mins(b: Seq<int>, len: int) -> int {
  if len <= 0 { 0 } else { b[0] + sum_mins(b.subrange(1, b.len() as int), len - 1) }
}

spec fn correct_result(n: int, b: Seq<int>, result: int) -> bool
  recommends valid_input(n, b)
{
  if n == 2 {
    result == 2 * b[0]
  } else {
    result == b[0] + b[n-2] + sum_mins(b, n-2)
  }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, b: Seq<int>) -> (result: int)
  requires valid_input(n, b)
  ensures correct_result(n, b, result)
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}