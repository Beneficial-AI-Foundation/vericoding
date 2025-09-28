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
    /* code modified by LLM (iteration 5): fixed compilation error by using ghost variable for heights_int */
    let n = n as usize;
    let k = k as usize;
    let mut min_idx: usize = 0;
    let mut min_sum: i32 = 0;
    let mut current_sum: i32 = 0;
    let ghost heights_int = heights@.map(|j: int, v: i8| v as int);
    
    // Calculate initial window sum
    let mut i: usize = 0;
    while i < k
        invariant
            i <= k,
            k <= n,
            n == heights.len(),
            current_sum == sum_window(heights_int, 0, i as int),
        decreases k - i
    {
        current_sum = current_sum + (heights[i] as i32);
        i = i + 1;
    }
    min_sum = current_sum;
    
    // Slide the window
    let mut start: usize = 1;
    while start <= n - k
        invariant
            1 <= start <= n - k + 1,
            k <= n,
            n == heights.len(),
            0 <= min_idx <= start - 1,
            min_idx <= n - k,
            current_sum == sum_window(heights_int, (start - 1) as int, k as int),
            min_sum == sum_window(heights_int, min_idx as int, k as int),
            forall|j: int| 0 <= j < start - 1 && j != min_idx ==> #[trigger] sum_window(heights_int, j, k as int) >= min_sum,
            forall|j: int| 0 <= j < min_idx ==> #[trigger] sum_window(heights_int, j, k as int) > min_sum,
        decreases n - k - start + 1
    {
        current_sum = current_sum - (heights[start - 1] as i32) + (heights[start + k - 1] as i32);
        if current_sum < min_sum {
            min_sum = current_sum;
            min_idx = start;
        }
        start = start + 1;
    }
    
    (min_idx + 1) as i8
}
// </vc-code>


}

fn main() {}