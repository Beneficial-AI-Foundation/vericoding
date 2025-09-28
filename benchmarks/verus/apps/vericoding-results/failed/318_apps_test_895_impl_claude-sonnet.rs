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
/* helper modified by LLM (iteration 5): fixed int casts by moving to ghost context */
fn max_loop_bound(times: &Vec<i8>) -> (result: i8)
    requires times@.len() >= 1
    ensures result >= 1,
            result <= 1000,
            forall|i: int| 0 <= i < times@.len() ==> times@[i] as int <= result as int
{
    let mut max_val = times[0];
    let mut i = 1;
    while i < times.len()
        invariant
            1 <= i <= times@.len(),
            max_val >= times@[0],
            max_val <= 1000,
            forall|j: int| 0 <= j < i ==> #[trigger] times@[j] as int <= max_val as int,
        decreases times@.len() - i
    {
        if times[i] > max_val {
            max_val = times[i];
        }
        i += 1;
    }
    max_val
}

fn count_in_window(times: &Vec<i8>, start: i8, T: i8) -> (result: i8)
    requires start >= 1,
             T >= 1,
             times@.len() >= 1,
             start as int + T as int - 1 <= 1000,
             forall|i: int| 0 <= i < times@.len() ==> 1 <= #[trigger] times@[i] as int <= 1000
    ensures result >= 0,
            result <= times@.len(),
            result as int == count_students_in_window(times@.map(|i, v| v as int), start as int, T as int)
{
    let mut count = 0;
    let mut i = 0;
    while i < times.len()
        invariant
            0 <= i <= times@.len(),
            count >= 0,
            count <= i,
            count as int == count_students_in_window_helper(times@.map(|j, v| v as int), start as int, T as int, i as int),
        decreases times@.len() - i
    {
        let ghost start_int = start as int;
        let ghost T_int = T as int;
        let ghost time_int = times[i] as int;
        if start <= times[i] && time_int <= start_int + T_int - 1 {
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, times: Vec<i8>, T: i8) -> (result: i8)
    requires valid_input(n as int, times@.map(|i, v| v as int), T as int)
    ensures result >= 0 && result <= n && result as int == max_students_in_window(times@.map(|i, v| v as int), T as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed int casts by moving to ghost context */
    let max_bound = max_loop_bound(&times);
    let mut max_count = 0;
    let mut start = 1;
    
    while start <= max_bound
        invariant
            1 <= start <= max_bound + 1,
            max_count >= 0,
            max_count <= n,
            max_count as int == max_students_in_window_up_to(times@.map(|i, v| v as int), T as int, (start - 1) as int),
        decreases max_bound - start + 1
    {
        let ghost start_int = start as int;
        let ghost T_int = T as int;
        if start_int + T_int - 1 <= 1000 {
            let current_count = count_in_window(&times, start, T);
            if current_count > max_count {
                max_count = current_count;
            }
        }
        start += 1;
    }
    
    max_count
}
// </vc-code>


}

fn main() {}