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
spec fn prefix_sum(heights: Seq<int>, n: int) -> int
  decreases n
{
  if n == 0 {
    0
  } else {
    prefix_sum(heights, n - 1) + heights[n - 1]
  }
}

/* helper modified by LLM (iteration 4): removed invalid int suffixes from literals */
fn lemma_prefix_step(heights: Seq<int>, index: int)
  requires
    0 <= index < heights.len()
  ensures
    prefix_sum(heights, index + 1) == prefix_sum(heights, index) + heights[index]
{
  // No implementation needed
}

/* helper modified by LLM (iteration 4): removed invalid int suffixes from literals */
fn lemma_sum_window_prefix(heights: Seq<int>, start: int, k: int)
  requires
    0 <= start && start + k <= heights.len() && k >= 0
  ensures
    sum_window(heights, start, k) == prefix_sum(heights, start + k) - prefix_sum(heights, start)
  decreases k
{
  if k == 0 {
    assert(sum_window(heights, start, k) == 0);
    assert(prefix_sum(heights, start + k) - prefix_sum(heights, start) == 0);
  } else {
    lemma_sum_window_prefix(heights, start + 1, k - 1);
    lemma_prefix_step(heights, start);
    assert(sum_window(heights, start, k) == heights[start] + sum_window(heights, start + 1, k - 1));
    assert(prefix_sum(heights, start + k) == prefix_sum(heights, start + k - 1) + heights[start + k - 1]);
    assert(prefix_sum(heights, start + k) - prefix_sum(heights, start) == heights[start] + (prefix_sum(heights, start + k) - prefix_sum(heights, start + 1)));
  }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, heights: Vec<i8>) -> (result: i8)
  requires valid_input(n as int, k as int, heights@.map(|i: int, v: i8| v as int))
  ensures valid_result(result as int, n as int, k as int, heights@.map(|i: int, v: i8| v as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): adjusted types to i32 for sums to fit without overflow */
{
  let sequences_heights: Vec<i32> = heights.iter().map(|&v| v as i32).collect();
  let n_int: usize = n as usize;
  let k_int: usize = k as usize;
  let mut p: Vec<i32> = Vec::with_capacity(n_int + 1);
  p.push(0);
  for i in 0..n_int {
    let next = p[i] + sequences_heights[i];
    p.push(next);
  }
  let mut min_sum: i32 = p[k_int] - p[0];
  let mut best_start: usize = 0;
  for s in 0..(n_int - k_int) {
    let current_sum = p[s + k_int + 1] - p[s + 1];
    if current_sum < min_sum {
      min_sum = current_sum;
      best_start = s + 1;
    }
  }
  return ((best_start as i32) + 1) as i8;
}
// </vc-code>


}

fn main() {}