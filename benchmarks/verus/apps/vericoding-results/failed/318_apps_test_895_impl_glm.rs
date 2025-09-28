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
/* helper modified by LLM (iteration 5): fixed index operator error by using split_first */
fn count_students_in_window_exec(times: &[i8], start: i32, T: i32) -> (count: i32)
    requires
        times.len() >= 0,
        T >= 1,
        forall|i: int| 0 <= i < times.len() ==> 1 <= times@[i] as int <= 1000,
        1 <= start as int <= 1000,
    ensures count as int == count_students_in_window(times@.map(|i, v| v as int), start as int, T as int)
    decreases times.len()
{
    if times.is_empty() {
        0
    } else {
        let (first, rest) = times.split_first().unwrap();
        let count_rest = count_students_in_window_exec(rest, start, T);
        let t0 = *first as i32;
        if start <= t0 && t0 <= start + T - 1 {
            count_rest + 1
        } else {
            count_rest
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, times: Vec<i8>, T: i8) -> (result: i8)
    requires valid_input(n as int, times@.map(|i, v| v as int), T as int)
    ensures result >= 0 && result <= n && result as int == max_students_in_window(times@.map(|i, v| v as int), T as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): unchanged from iteration 4 */
{
    let mut max_count = 0;
    let mut start = 1i32;
    while start <= 1000
        invariant
            1 <= start as int,
            start as int <= 1001,
            max_count as int == max_students_in_window_up_to(times@.map(|i, v| v as int), T as int, (start-1) as int),
        decreases (1000i32 - start) as int
    {
        let count = count_students_in_window_exec(&times, start, T as i32);
        if count > max_count {
            max_count = count;
        }
        start += 1;
    }
    max_count as i8
}
// </vc-code>


}

fn main() {}