// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, times: Seq<int>, T: int) -> bool {
    n >= 1 && times.len() == n && T >= 1 && 
    forall|i: int| 0 <= i < times.len() ==> 1 <= #[trigger] times[i] <= 1000
}

spec fn max_students_in_window(times: Seq<int>, T: int) -> int {
    max_students_in_window_up_to(times, T, 1000)
}

spec fn max_students_in_window_up_to(times: Seq<int>, T: int, max_start: int) -> int
    decreases max_start
{
    if max_start < 1 { 
        0
    } else {
        let count = count_students_in_window(times, max_start, T);
        let rest_max = max_students_in_window_up_to(times, T, max_start - 1);
        if count > rest_max { count } else { rest_max }
    }
}

spec fn count_students_in_window(times: Seq<int>, start: int, T: int) -> int {
    if times.len() == 0 { 
        0 
    } else { 
        count_students_in_window_helper(times, start, T, 0) 
    }
}

spec fn count_students_in_window_helper(times: Seq<int>, start: int, T: int, index: int) -> int
    decreases times.len() - index
{
    if index >= times.len() { 
        0
    } else {
        let count_rest = count_students_in_window_helper(times, start, T, index + 1);
        if start <= times[index] <= start + T - 1 { 
            count_rest + 1 
        } else { 
            count_rest 
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed. */
fn max(a: i8, b: i8) -> i8 { if a > b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, times: Vec<i8>, T: i8) -> (result: i8)
    requires valid_input(n as int, times@.map(|i, v| v as int), T as int)
    ensures result >= 0 && result <= n && result as int == max_students_in_window(times@.map(|i, v| v as int), T as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Cast `times_seq[i]` to `int` within ghost contexts to address verification errors related to `nat`/`int` usage in non-ghost code. */
{
    let times_seq = times@;

    let mut max_count: i8 = 0;

    let mut start: i16 = 1;
    while start <= 1000
        invariant
            1 <= start,
            start <= 1001,
            (max_count as int) == max_students_in_window_up_to(times@.map(|i,v| v as int), T as int, (start - 1) as int),
            max_count >= 0,
            max_count <= n,
        decreases 1001 - start
    {
        let mut current_count: i8 = 0;
        let mut i: i8 = 0;
        while i < n
            invariant
                0 <= i,
                i <= n,
                (current_count as int) == count_students_in_window_helper(times@.map(|k,v| v as int), start as int, T as int, i as int),
                current_count >= 0,
                current_count <= n,
            decreases n - i
        {
            if start as int <= times_seq[i as int] as int && times_seq[i as int] as int <= (start + T - 1) as int {
                current_count = current_count + 1;
            }
            i = i + 1;
        }

        if current_count > max_count {
            max_count = current_count;
        }
        start = start + 1;
    }
    max_count
}
// </vc-code>


}

fn main() {}