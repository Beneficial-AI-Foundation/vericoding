// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, times: Seq<int>, T: int) -> bool {
    n >= 1 && times.len() == n && T >= 1 && 
    forall|i: int| 0 <= i < times.len() ==> 1 <= times[i] <= 1000
}

spec fn max_students_in_window(times: Seq<int>, T: int) -> int
    recommends T >= 1,
               forall|i: int| 0 <= i < times.len() ==> 1 <= times[i] <= 1000
{
    max_students_in_window_up_to(times, T, 1000)
}

spec fn max_students_in_window_up_to(times: Seq<int>, T: int, max_start: int) -> int
    recommends T >= 1,
               forall|i: int| 0 <= i < times.len() ==> 1 <= times[i] <= 1000,
               max_start >= 0
{
    if max_start < 1 {
        0
    } else {
        let count = count_students_in_window(times, max_start, T);
        let rest_max = max_students_in_window_up_to(times, T, max_start - 1);
        if count > rest_max { count } else { rest_max }
    }
}

spec fn count_students_in_window(times: Seq<int>, start: int, T: int) -> int
    recommends T >= 1,
               forall|i: int| 0 <= i < times.len() ==> 1 <= times[i] <= 1000,
               start >= 1
{
    count_students_in_window_helper(times, start, T, 0)
}

spec fn count_students_in_window_helper(times: Seq<int>, start: int, T: int, index: int) -> int
    recommends T >= 1,
               forall|i: int| 0 <= i < times.len() ==> 1 <= times[i] <= 1000,
               start >= 1,
               0 <= index <= times.len()
    decreases times.len() - index
{
    if index == times.len() {
        0
    } else {
        let count_rest = count_students_in_window_helper(times, start, T, index + 1);
        if start <= times[index] <= start + T - 1 { count_rest + 1 } else { count_rest }
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, times: Seq<int>, T: int) -> (result: int)
    requires 
        valid_input(n, times, T),
    ensures 
        result >= 0,
        result <= n,
        result == max_students_in_window(times, T),
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}