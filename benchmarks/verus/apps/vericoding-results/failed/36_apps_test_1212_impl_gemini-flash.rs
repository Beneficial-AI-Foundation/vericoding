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
/* helper modified by LLM (iteration 5): Removed all content as no helpers are truly needed and the placeholder was causing compilation errors. There should be nothing in the helper section. */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, heights: Vec<i8>) -> (result: i8)
  requires valid_input(n as int, k as int, heights@.map(|i: int, v: i8| v as int))
  ensures valid_result(result as int, n as int, k as int, heights@.map(|i: int, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation errors related to `int` and `nat` types in `ghost` contexts and correctly cast `i` to `usize` for array indexing. */
    let ghost n_int = n as int;
    let ghost k_int = k as int;
    let heights_seq = heights@.map(|_i: int, v: i8| v as int);

    let mut min_sum_val: i32 = 0;
    let mut min_idx_val: i8 = 0;
    let mut current_sum_val: i32 = 0;

    if k > 0 {
        for j in 0..k as usize {
            min_sum_val += heights[j] as i32;
        }
    }

    current_sum_val = min_sum_val;

    let mut i: i8 = 1;
    while (i as int) <= n_int - k_int
        invariant
            0 < i as int,
            (i as int) <= n_int - k_int + 1,
            0 <= min_idx_val as int,
            (min_idx_val as int) < (i as int),
            min_sum_val as int == sum_window(heights_seq, min_idx_val as int, k_int),
            forall|j: int| 0 <= j < i as int ==> sum_window(heights_seq, min_idx_val as int, k_int) <= sum_window(heights_seq, j, k_int),
            current_sum_val as int == sum_window(heights_seq, (i - 1) as int, k_int),

            1 <= k as int,
            k as int <= n as int,
            heights_seq.len() == n as int,
            forall|idx: int| 0 <= idx < n as int ==> (1 <= #[trigger] heights_seq[idx] <= 100)
        decreases (n_int - k_int) - (i as int)
    {
        proof {
            if (i - 1) as int + k_int < n_int {
                assert(heights_seq[(i - 1) as int] >= 1);
                assert(heights_seq[(i - 1) as int] <= 100);
                assert(heights_seq[(i - 1) as int + k_int] >= 1);
                assert(heights_seq[(i - 1) as int + k_int] <= 100);
            }
        }

        current_sum_val = current_sum_val - (heights[(i - 1) as usize] as i32) + (heights[(i - 1 + k) as usize] as i32);

        if current_sum_val < min_sum_val {
            min_sum_val = current_sum_val;
            min_idx_val = i;
        }
        i = i + 1;
    }

    (min_idx_val + 1) as i8
}
// </vc-code>


}

fn main() {}