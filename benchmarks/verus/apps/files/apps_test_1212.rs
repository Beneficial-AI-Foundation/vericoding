// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn sum_window(heights: Seq<int>, start: int, k: int) -> int
  decreases k
{
  if 0 <= start && start + k <= heights.len() && k > 0 {
    if k == 1 { heights[start] }
    else { heights[start] + sum_window(heights, start + 1, k - 1) }
  } else {
    0
  }
}

spec fn valid_input(n: int, k: int, heights: Seq<int>) -> bool
{
  1 <= k <= n && heights.len() == n && forall|i: int| 0 <= i < n ==> (1 <= #[trigger] heights[i] <= 100)
}

spec fn valid_result(result: int, n: int, k: int, heights: Seq<int>) -> bool
{
  &&& valid_input(n, k, heights)
  &&& 1 <= result <= n-k+1
  &&& (forall|start: int| 0 <= start <= n-k ==> 
        sum_window(heights, result-1, k) <= #[trigger] sum_window(heights, start, k))
  &&& (forall|start: int| 0 <= start < result-1 ==>
        #[trigger] sum_window(heights, start, k) > sum_window(heights, result-1, k))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, heights: Vec<i8>) -> (result: i8)
  requires valid_input(n as int, k as int, heights@.map(|i: int, v: i8| v as int))
  ensures valid_result(result as int, n as int, k as int, heights@.map(|i: int, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
  assume(false);
  unreached()
}
// </vc-code>


}

fn main() {}