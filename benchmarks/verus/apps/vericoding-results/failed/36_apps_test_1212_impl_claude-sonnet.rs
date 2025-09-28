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
/* helper modified by LLM (iteration 5): fixed int literal type annotations */
fn lemma_sum_window_bounds(heights: Seq<int>, start: int, k: int)
    requires
        0 <= start,
        start + k <= heights.len(),
        k > 0,
        forall|i: int| 0 <= i < heights.len() ==> 1 <= #[trigger] heights[i] <= 100,
    ensures
        k <= sum_window(heights, start, k) <= 100 * k,
    decreases k
{
    if k == 1int {
        assert(sum_window(heights, start, k) == heights[start]);
    } else {
        lemma_sum_window_bounds(heights, start + 1int, k - 1int);
        assert(sum_window(heights, start, k) == heights[start] + sum_window(heights, start + 1int, k - 1int));
    }
}

fn lemma_sum_window_valid(heights: Seq<int>, start: int, k: int)
    requires
        0 <= start,
        start + k <= heights.len(),
        k > 0,
    ensures
        sum_window(heights, start, k) == sum_window(heights, start, k),
{
}

fn compute_sum_window(heights: &Vec<i8>, start: usize, k: usize) -> (sum: i32)
    requires
        start + k <= heights@.len(),
        k > 0,
    ensures
        sum == sum_window(heights@.map(|i: int, v: i8| v as int), start as int, k as int),
{
    let mut sum = 0i32;
    let mut i = 0usize;
    while i < k
        invariant
            i <= k,
            start + k <= heights@.len(),
            sum == sum_window(heights@.map(|i: int, v: i8| v as int), start as int, i as int),
    {
        sum = sum + heights[start + i] as i32;
        i = i + 1;
    }
    sum
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, heights: Vec<i8>) -> (result: i8)
  requires valid_input(n as int, k as int, heights@.map(|i: int, v: i8| v as int))
  ensures valid_result(result as int, n as int, k as int, heights@.map(|i: int, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed int literal type annotations */
    let ghost spec_heights = heights@.map(|i: int, v: i8| v as int);
    let mut best_start = 0usize;
    let mut best_sum = compute_sum_window(&heights, 0, k as usize);
    
    proof {
        lemma_sum_window_bounds(spec_heights, 0, k as int);
    }
    
    let mut current_start = 1usize;
    
    while current_start <= (n - k) as usize
        invariant
            1 <= current_start <= (n - k + 1) as usize,
            best_start < current_start,
            best_sum == sum_window(spec_heights, best_start as int, k as int),
            forall|start: int| 0 <= start < current_start ==> 
                sum_window(spec_heights, best_start as int, k as int) <= #[trigger] sum_window(spec_heights, start, k as int),
            forall|start: int| 0 <= start < best_start ==> 
                #[trigger] sum_window(spec_heights, start, k as int) > sum_window(spec_heights, best_start as int, k as int),
    {
        let current_sum = compute_sum_window(&heights, current_start, k as usize);
        
        if current_sum < best_sum {
            best_start = current_start;
            best_sum = current_sum;
        }
        
        current_start = current_start + 1;
    }
    
    (best_start + 1) as i8
}
// </vc-code>


}

fn main() {}