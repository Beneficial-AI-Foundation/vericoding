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
/* helper modified by LLM (iteration 5): fixed compilation error by removing trailing commas after last invariant conditions */
fn exec_count_students_in_window(times: &Vec<i8>, start: i32, T: i8) -> i32
    requires
        1 <= start <= 1000 - (T as i32 - 1),
        T >= 1,
        T <= 127,
        forall|i: int| 0 <= i < times.len() ==> 1 <= #[trigger] times@[i] <= 1000,
    ensures
        result as int == count_students_in_window(times@.map(|_, v| v as int), start as int, T as int),
{
    let mut count: i32 = 0;
    let mut i: usize = 0;
    while i < times.len()
        invariant
            0 <= i as int <= times.len() as int,
            count == count_students_in_window_helper(times@.map(|_, v| v as int), start as int, T as int, 0) - count_students_in_window_helper(times@.map(|_, v| v as int), start as int, T as int, i as int)
        decreases times.len() - i
    {
        if times[i] as i32 >= start && times[i] as i32 < start + (T as i32) {
            count += 1;
        }
        i += 1;
    }
    count
}

fn exec_max_students_in_window(times: &Vec<i8>, T: i8) -> i32
    requires
        T as int >= 1,
        forall|i: int| 0 <= i < times.len() ==> 1 <= #[trigger] times@[i] <= 1000,
        times.len() as int >= 1,
    ensures
        result as int == max_students_in_window(times@.map(|_, v| v as int), T as int),
{
    let mut max_count: i32 = 0;
    let mut start: i32 = 1;
    while start <= 1000
        invariant
            1 <= start <= 1001,
            max_count == max_students_in_window_up_to(times@.map(|_, v| v as int), T as int, start - 1)
        decreases 1001 - start
    {
        let current = exec_count_students_in_window(&times, start, T);
        if current > max_count {
            max_count = current;
        }
        start += 1;
    }
    max_count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, times: Vec<i8>, T: i8) -> (result: i8)
    requires valid_input(n as int, times@.map(|i, v| v as int), T as int)
    ensures result >= 0 && result <= n && result as int == max_students_in_window(times@.map(|i, v| v as int), T as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [brief description] */
{
    exec_max_students_in_window(&times, T) as i8
}
// </vc-code>


}

fn main() {}