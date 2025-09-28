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
/* helper modified by LLM (iteration 4): renamed 'start' parameter to 'start_time' to avoid compilation errors */
proof fn compute_count(times: &Vec<i8>, n: i8, ghost start_time: int, ghost T_val: int) -> (current_students: int)
    requires
        times.len() == n as int,
        T_val >= 1,
        forall|i: int| 0 <= i < times.len() ==> 1 <= #[trigger] times@[i] as int <= 1000,
    ensures
        current_students == count_students_in_window(times@.map(|_i, v| v as int), start_time, T_val),
{
    ghost let times_spec = times@.map(|_i, v| v as int);
    ghost let n_spec = n as int;

    ghost let mut current_students: int = 0;
    let mut i: usize = 0;

    proof {
        reveal_with_fuel(count_students_in_window, 2);
    }

    while i < n as usize
        invariant
            i <= n as usize,
            times@.map(|_i, v| v as int) == times_spec,
            n as int == n_spec,
            T_val >= 1,
            current_students + count_students_in_window_helper(times_spec, start_time, T_val, i as int) == count_students_in_window(times_spec, start_time, T_val),
        decreases (n as usize) - i
    {
        proof {
            reveal_with_fuel(count_students_in_window_helper, 2);
        }
        let time = times[i];
        ghost let time_spec = time as int;
        
        if start_time <= time_spec && time_spec <= start_time + T_val - 1 {
            current_students = current_students + 1;
        }
        i = i + 1;
    }

    proof {
        reveal_with_fuel(count_students_in_window_helper, 2);
        assert(count_students_in_window_helper(times_spec, start_time, T_val, n_spec) == 0);
    }
    current_students
}

/* helper modified by LLM (iteration 4): renamed 'start' parameter to 'start_time' to be consistent */
proof fn lemma_count_helper_le_len(times: Seq<int>, start_time: int, T: int, index: int)
    requires 0 <= index <= times.len(),
    ensures count_students_in_window_helper(times, start_time, T, index) <= times.len() - index,
    decreases times.len() - index
{
    reveal_with_fuel(count_students_in_window_helper, 2);
    if index < times.len() {
        lemma_count_helper_le_len(times, start_time, T, index + 1);
    }
}

proof fn lemma_max_students_window_le_len(times: Seq<int>, T: int, max_start: int)
    requires
        times.len() >= 0,
        T >= 1,
        forall|i: int| 0 <= i < times.len() ==> 1 <= #[trigger] times[i] <= 1000,
    ensures
        max_students_in_window_up_to(times, T, max_start) <= times.len(),
    decreases max_start
{
    reveal_with_fuel(max_students_in_window_up_to, 2);
    if max_start >= 1 {
        lemma_max_students_window_le_len(times, T, max_start - 1);
        let count = count_students_in_window(times, max_start, T);

        reveal_with_fuel(count_students_in_window, 2);
        lemma_count_helper_le_len(times, max_start, T, 0);
        assert(count <= times.len());
        
        let rest_max = max_students_in_window_up_to(times, T, max_start - 1);
        assert(rest_max <= times.len());
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
    /* code modified by LLM (iteration 4): renamed 'start' variable to 'start_time' to avoid potential compilation conflicts */
    ghost let times_spec = times@.map(|_i, v| v as int);
    ghost let T_spec = T as int;
    ghost let n_spec = n as int;

    let mut start_time: i32 = 1;
    ghost let mut max_students: int = 0;
    
    proof {
        reveal_with_fuel(max_students_in_window_up_to, 2);
    }

    while start_time <= 1000
        invariant
            1 <= start_time <= 1001,
            times@.map(|_i, v| v as int) == times_spec,
            n as int == n_spec,
            T as int == T_spec,
            valid_input(n_spec, times_spec, T_spec),
            max_students == max_students_in_window_up_to(times_spec, T_spec, start_time as int - 1),
        decreases 1001 - start_time
    {
        ghost let current_students = compute_count(&times, n, start_time as int, T_spec);
        
        if current_students > max_students {
            max_students = current_students;
        }

        proof {
            reveal_with_fuel(max_students_in_window_up_to, 2);
        }
        start_time = start_time + 1;
    }

    assert(max_students == max_students_in_window(times_spec, T_spec)) by {
        assert(start_time == 1001);
        reveal_with_fuel(max_students_in_window, 2);
        assert(max_students == max_students_in_window_up_to(times_spec, T_spec, 1000));
        assert(max_students_in_window(times_spec, T_spec) == max_students_in_window_up_to(times_spec, T_spec, 1000));
    };

    lemma_max_students_window_le_len(times_spec, T_spec, 1000);
    
    assert(max_students <= n_spec) by {
        reveal_with_fuel(max_students_in_window, 2);
        assert(max_students == max_students_in_window_up_to(times_spec, T_spec, 1000));
    };

    max_students as i8
}
// </vc-code>


}

fn main() {}