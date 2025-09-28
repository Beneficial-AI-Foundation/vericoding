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
/* helper modified by LLM (iteration 5): telescoping lemma for sum_window to extend window by one element */
proof fn lemma_extend_sum_window(heights: Seq<int>, start: int, t: int)
    requires
        0 <= start,
        0 <= t,
        start + t + 1 <= heights.len(),
    ensures
        sum_window(heights, start, t + 1) == sum_window(heights, start, t) + heights[start + t],
    decreases t
{
    if t == 0 {
        assert(sum_window(heights, start, 1) == heights[start]);
        assert(sum_window(heights, start, 0) == 0);
        assert(sum_window(heights, start, 1) == sum_window(heights, start, 0) + heights[start + 0]);
    } else {
        lemma_extend_sum_window(heights, start + 1, t - 1);
        assert(sum_window(heights, start, t) == heights[start] + sum_window(heights, start + 1, t - 1));
        assert(sum_window(heights, start, t + 1) == heights[start] + sum_window(heights, start + 1, t));
        assert(sum_window(heights, start + 1, t) == sum_window(heights, start + 1, t - 1) + heights[start + t]);
        assert(sum_window(heights, start, t + 1) == sum_window(heights, start, t) + heights[start + t]);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, heights: Vec<i8>) -> (result: i8)
  requires valid_input(n as int, k as int, heights@.map(|i: int, v: i8| v as int))
  ensures valid_result(result as int, n as int, k as int, heights@.map(|i: int, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement O(n*k) search with invariants ensuring minimal earliest window; fix parsing by adding parentheses and simplifying conditions */
    let ni: i32 = n as i32;
    let ki: i32 = k as i32;

    let mapped: Seq<int> = heights@.map(|i: int, v: i8| v as int);

    proof {
        assert(1 <= k as int && k as int <= n as int);
        assert(heights.len() as int == n as int);
    }

    let total: i32 = ni - ki + 1;
    proof {
        assert(total as int == n as int - k as int + 1);
        assert(1 <= k as int && k as int <= n as int);
        assert(n as int - k as int + 1 >= 1);
    }

    let mut start: i32 = 0;
    let mut best_start: i32 = 0;
    let mut best_sum: i32 = 0;
    let mut found: bool = false;

    while start < total
        invariant
            0 <= start as int,
            start as int <= total as int,
            (!found) || (0 <= best_start as int),
            (!found) || ((best_start as int) < (start as int)),
            (!found) || (best_sum as int == sum_window(mapped, best_start as int, ki as int)),
            (!found) || (forall|j: int| 0 <= j && j < start as int ==> best_sum as int <= sum_window(mapped, j, ki as int)),
            (!found) || (forall|j: int| 0 <= j && j < best_start as int ==> sum_window(mapped, j, ki as int) > best_sum as int),
        decreases (total as int) - (start as int)
    {
        proof {
            assert(start as int < total as int);
            assert(total as int == n as int - k as int + 1);
            assert(start as int <= n as int - k as int);
            assert(start as int + k as int <= n as int);
            assert(heights.len() as int == n as int);
            assert(start as int + k as int <= heights.len() as int);
        }

        let mut s: i32 = 0;
        let mut t: i32 = 0;
        while t < ki
            invariant
                0 <= t as int,
                t as int <= ki as int,
                s as int == sum_window(mapped, start as int, t as int),
                0 <= start as int,
                start as int + t as int <= heights.len() as int,
            decreases (ki as int) - (t as int)
        {
            proof {
                assert(t as int < ki as int);
                assert(start as int + ki as int <= heights.len() as int);
                assert(start as int + t as int + 1 <= start as int + ki as int);
                assert(start as int + t as int + 1 <= heights.len() as int);
            }
            let idx: usize = (start + t) as usize;
            s = s + heights[idx] as i32;
            proof {
                let i_int: int = start as int + t as int;
                assert(0 <= i_int && i_int < heights.len() as int);
                assert(heights@[i_int] == heights[idx]);
                assert(mapped[i_int] == heights@[i_int] as int);
                lemma_extend_sum_window(mapped, start as int, t as int);
                assert(sum_window(mapped, start as int, t as int + 1) == sum_window(mapped, start as int, t as int) + mapped[i_int]);
                assert(s as int == sum_window(mapped, start as int, t as int) + mapped[i_int]);
            }
            t = t + 1;
            proof {
                assert(s as int == sum_window(mapped, start as int, t as int));
            }
        }
        proof {
            assert(s as int == sum_window(mapped, start as int, ki as int));
        }

        if !found {
            best_sum = s;
            best_start = start;
            found = true;
        } else {
            if (s as int) < (best_sum as int) {
                best_sum = s;
                best_start = start;
            } else {
                proof { assert(s as int >= best_sum as int); }
            }
        }

        proof { assert(found); }
        start = start + 1;
    }

    proof { assert(found); }
    let result_int: i32 = best_start + 1;
    proof {
        assert(1 <= result_int as int);
        assert(result_int as int <= total as int);
    }
    let result_i8: i8 = result_int as i8;

    proof {
        // Show valid_result(result, n, k, mapped)
        assert(valid_input(n as int, k as int, mapped));
        // Range
        assert(1 <= result_int as int && result_int as int <= n as int - k as int + 1);
        // Minimality over all windows
        assert(forall|j: int| 0 <= j && j < total as int ==> best_sum as int <= sum_window(mapped, j, ki as int));
        assert(forall|j: int| 0 <= j && j < best_start as int ==> sum_window(mapped, j, ki as int) > best_sum as int);
        // Relate result to best_start
        assert(result_i8 as int - 1 == best_start as int);
    }

    result_i8
}
// </vc-code>


}

fn main() {}