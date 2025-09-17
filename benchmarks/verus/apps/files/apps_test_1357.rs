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
fn solve(n: int, m: int, tasks: Seq<int>) -> (result: int)
    requires valid_input(n, m, tasks)
    ensures 
        result >= 0,
        m > 0 ==> result >= tasks[m-1] - 1,
        result <= (m - 1) * n + tasks[m-1] - 1,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}