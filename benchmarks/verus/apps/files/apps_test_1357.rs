// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, tasks: Seq<int>) -> bool {
    n >= 2 && m >= 1 && tasks.len() == m && 
    forall|i: int| 0 <= i < tasks.len() ==> 1 <= #[trigger] tasks[i] <= n
}

spec fn min_time_to_complete(n: int, tasks: Seq<int>, current_pos: int, task_index: int) -> int
    recommends 
        n >= 2,
        forall|i: int| 0 <= i < tasks.len() ==> 1 <= #[trigger] tasks[i] <= n,
        1 <= current_pos <= n,
        0 <= task_index < tasks.len()
{
    let target = tasks[task_index];
    if target >= current_pos { target - current_pos }
    else { (n - current_pos) + target }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, tasks: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, m as int, tasks@.map(|i, x: i8| x as int))
    ensures 
        result >= 0,
        m > 0 ==> result >= tasks@[(m as int) - 1] as int - 1,
        result <= ((m as int) - 1) * (n as int) + tasks@[(m as int) - 1] as int - 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}