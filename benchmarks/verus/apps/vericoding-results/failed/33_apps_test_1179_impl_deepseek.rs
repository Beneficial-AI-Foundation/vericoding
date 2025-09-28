// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, l: Seq<int>) -> bool {
    n >= 1 && k >= 1 && l.len() == n && k <= n * (n + 1) / 2
}

spec fn total_identifiers_after_robot(i: int) -> int 
    recommends i >= 0
{
    i * (i + 1) / 2
}

spec fn correct_result(n: int, k: int, l: Seq<int>, result: int) -> bool
    recommends valid_input(n, k, l)
{
    exists|i: int| #[trigger] total_identifiers_after_robot(i) > 0 &&
      1 <= i <= n && 
      total_identifiers_after_robot(i - 1) < k <= total_identifiers_after_robot(i) &&
      result == l[k - total_identifiers_after_robot(i - 1) - 1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add helper function to compute total identifiers */
proof fn compute_total_identifiers(i: int) -> (res: int)
    requires i >= 0
    ensures res == i * (i + 1) / 2
    decreases i
{
    if i == 0 {
        0
    } else {
        let prev = compute_total_identifiers(i - 1);
        prev + i
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, l: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, k as int, l@.map(|i: int, x: i8| x as int))
    ensures correct_result(n as int, k as int, l@.map(|i: int, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Add decreases clause to while loop */
{
    let mut robot_index: i8 = 0;
    let mut cumulative_total: i32 = 0;
    
    while robot_index < n
        invariant
            robot_index >= 0,
            robot_index <= n,
            cumulative_total == total_identifiers_after_robot(robot_index as int),
        decreases n - robot_index
    {
        robot_index += 1;
        let next_total: i32 = cumulative_total + robot_index as i32;
        
        if next_total >= k as i32 {
            let pos: i32 = k as i32 - cumulative_total - 1;
            return l[pos as usize];
        }
        
        cumulative_total = next_total;
    }
    
    0
}
// </vc-code>


}

fn main() {}