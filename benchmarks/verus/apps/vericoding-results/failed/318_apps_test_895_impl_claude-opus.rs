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
/* helper modified by LLM (iteration 4): Fixed helper to count from 0 to index instead of index to end */
spec fn count_up_to(times: Seq<int>, start: int, T: int, index: int) -> int
    decreases index
{
    if index <= 0 {
        0
    } else {
        let count_rest = count_up_to(times, start, T, index - 1);
        if start <= times[index - 1] <= start + T - 1 {
            count_rest + 1
        } else {
            count_rest
        }
    }
}

proof fn lemma_count_up_to_equals_helper(times: Seq<int>, start: int, T: int)
    requires
        times.len() >= 0,
        T >= 1,
    ensures
        count_up_to(times, start, T, times.len()) == count_students_in_window(times, start, T),
    decreases times.len()
{
    if times.len() == 0 {
        assert(count_up_to(times, start, T, 0) == 0);
        assert(count_students_in_window(times, start, T) == 0);
    } else {
        lemma_count_helper_equals(times, start, T, 0);
    }
}

proof fn lemma_count_helper_equals(times: Seq<int>, start: int, T: int, index: int)
    requires
        times.len() > 0,
        T >= 1,
        0 <= index <= times.len(),
    ensures
        count_up_to(times, start, T, times.len()) - count_up_to(times, start, T, index) == count_students_in_window_helper(times, start, T, index),
    decreases times.len() - index
{
    if index >= times.len() {
        assert(count_students_in_window_helper(times, start, T, index) == 0);
    } else {
        lemma_count_helper_equals(times, start, T, index + 1);
    }
}

proof fn lemma_max_students_bounded(times: Seq<int>, T: int, max_start: int)
    requires
        times.len() >= 1,
        T >= 1,
        forall|i: int| 0 <= i < times.len() ==> 1 <= #[trigger] times[i] <= 127,
    ensures
        max_students_in_window_up_to(times, T, max_start) <= times.len(),
    decreases max_start
{
    if max_start < 1 {
        assert(max_students_in_window_up_to(times, T, max_start) == 0);
    } else {
        lemma_count_students_bounded(times, max_start, T);
        lemma_max_students_bounded(times, T, max_start - 1);
    }
}

proof fn lemma_count_students_bounded(times: Seq<int>, start: int, T: int)
    requires
        times.len() >= 1,
        T >= 1,
        forall|i: int| 0 <= i < times.len() ==> 1 <= #[trigger] times[i] <= 127,
    ensures
        count_students_in_window(times, start, T) <= times.len(),
{
    if times.len() == 0 {
        assert(count_students_in_window(times, start, T) == 0);
    } else {
        lemma_count_students_helper_bounded(times, start, T, 0);
    }
}

proof fn lemma_count_students_helper_bounded(times: Seq<int>, start: int, T: int, index: int)
    requires
        times.len() >= 1,
        T >= 1,
        0 <= index <= times.len(),
        forall|i: int| 0 <= i < times.len() ==> 1 <= #[trigger] times[i] <= 127,
    ensures
        count_students_in_window_helper(times, start, T, index) <= times.len() - index,
    decreases times.len() - index
{
    if index >= times.len() {
        assert(count_students_in_window_helper(times, start, T, index) == 0);
    } else {
        lemma_count_students_helper_bounded(times, start, T, index + 1);
    }
}

proof fn lemma_max_found_at_time(times: Seq<int>, T: int, t: int)
    requires
        times.len() >= 1,
        T >= 1,
        1 <= t <= 127,
        forall|i: int| 0 <= i < times.len() ==> 1 <= #[trigger] times[i] <= 127,
    ensures
        max_students_in_window_up_to(times, T, t) >= count_students_in_window(times, t, T),
    decreases t
{
    if t < 1 {
        assert(max_students_in_window_up_to(times, T, t) == 0);
    } else if t == 1 {
        assert(max_students_in_window_up_to(times, T, 1) >= count_students_in_window(times, 1, T));
    } else {
        lemma_max_found_at_time(times, T, t - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, times: Vec<i8>, T: i8) -> (result: i8)
    requires valid_input(n as int, times@.map(|i, v| v as int), T as int)
    ensures result >= 0 && result <= n && result as int == max_students_in_window(times@.map(|i, v| v as int), T as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed invariant and arithmetic overflow issues */
    let mut max_count: i8 = 0;
    let mut start_time: i8 = 1;
    
    let ghost times_int = times@.map(|i, v| v as int);
    let max_time: i8 = 127;
    let end_time: i8 = if max_time >= T { max_time - T + 1 } else { 1 };
    
    while start_time <= end_time
        invariant
            1 <= start_time <= end_time + 1,
            0 <= max_count <= n,
            max_count as int == max_students_in_window_up_to(times_int, T as int, (start_time - 1) as int),
            times_int == times@.map(|i, v| v as int),
            valid_input(n as int, times_int, T as int),
            end_time == if 127 >= T as int { 127 - T as int + 1 } else { 1 },
            T >= 1,
            start_time + T - 1 <= 127,
        decreases end_time as int - start_time as int + 1
    {
        let mut count: i8 = 0;
        let mut i: usize = 0;
        let window_end: i8 = if start_time <= 127 - T + 1 { start_time + T - 1 } else { 127 };
        
        while i < times.len()
            invariant
                0 <= i <= times.len(),
                0 <= count <= n,
                count as int == count_up_to(times_int, start_time as int, T as int, i as int),
                times_int == times@.map(|i, v| v as int),
                valid_input(n as int, times_int, T as int),
                1 <= start_time <= end_time,
                window_end == if start_time <= 127 - T + 1 { start_time + T - 1 } else { 127 },
                window_end <= 127,
            decreases times.len() - i
        {
            if times[i] >= start_time && times[i] <= window_end {
                count = count + 1;
            }
            i = i + 1;
        }
        
        proof {
            lemma_count_up_to_equals_helper(times_int, start_time as int, T as int);
            assert(count as int == count_students_in_window(times_int, start_time as int, T as int));
        }
        
        if count > max_count {
            max_count = count;
        }
        
        proof {
            if start_time <= 127 {
                lemma_max_found_at_time(times_int, T as int, start_time as int);
            }
        }
        
        start_time = start_time + 1;
    }
    
    // Continue checking remaining windows if needed
    while start_time <= max_time && start_time > end_time
        invariant
            end_time < start_time <= max_time + 1,
            0 <= max_count <= n,
            max_count as int == max_students_in_window_up_to(times_int, T as int, (start_time - 1) as int),
            times_int == times@.map(|i, v| v as int),
            valid_input(n as int, times_int, T as int),
            T >= 1,
        decreases max_time as int - start_time as int + 1
    {
        let mut count: i8 = 0;
        let mut i: usize = 0;
        let window_end: i8 = if start_time <= 127 - T + 1 { start_time + T - 1 } else { 127 };
        
        while i < times.len()
            invariant
                0 <= i <= times.len(),
                0 <= count <= n,
                count as int == count_up_to(times_int, start_time as int, T as int, i as int),
                times_int == times@.map(|i, v| v as int),
                valid_input(n as int, times_int, T as int),
                start_time <= max_time,
                window_end == if start_time <= 127 - T + 1 { start_time + T - 1 } else { 127 },
                window_end <= 127,
            decreases times.len() - i
        {
            if times[i] >= start_time && times[i] <= window_end {
                count = count + 1;
            }
            i = i + 1;
        }
        
        proof {
            lemma_count_up_to_equals_helper(times_int, start_time as int, T as int);
            assert(count as int == count_students_in_window(times_int, start_time as int, T as int));
        }
        
        if count > max_count {
            max_count = count;
        }
        
        proof {
            if start_time <= 127 {
                lemma_max_found_at_time(times_int, T as int, start_time as int);
            }
        }
        
        start_time = start_time + 1;
    }
    
    // Check windows beyond 127 up to 1000 if needed
    proof {
        assert(max_count as int == max_students_in_window_up_to(times_int, T as int, 127));
        // Since all times are <= 1000 in spec but we use i8 (max 127),
        // we've checked all relevant windows
        assert(forall|t: int| 128 <= t <= 1000 ==> count_students_in_window(times_int, t, T as int) == 0);
        assert(max_students_in_window_up_to(times_int, T as int, 1000) == max_students_in_window_up_to(times_int, T as int, 127));
        assert(max_count as int == max_students_in_window(times_int, T as int));
        lemma_max_students_bounded(times_int, T as int, 127);
    }
    
    max_count
}
// </vc-code>


}

fn main() {}