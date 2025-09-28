// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, r: Seq<int>, b: Seq<int>) -> bool {
    n > 0 && r.len() == n && b.len() == n &&
    (forall|i: int| 0 <= i < n ==> (r[i] == 0 || r[i] == 1)) &&
    (forall|i: int| 0 <= i < n ==> (b[i] == 0 || b[i] == 1))
}

spec fn robot_advantage_count(n: int, r: Seq<int>, b: Seq<int>) -> int {
    Set::new(|i: int| 0 <= i < n && r[i] == 1 && b[i] == 0).len() as int
}

spec fn opponent_advantage_count(n: int, r: Seq<int>, b: Seq<int>) -> int {
    Set::new(|i: int| 0 <= i < n && r[i] == 0 && b[i] == 1).len() as int
}

spec fn can_win(n: int, r: Seq<int>, b: Seq<int>) -> bool {
    robot_advantage_count(n, r, b) > 0
}

spec fn min_max_point_value(n: int, r: Seq<int>, b: Seq<int>) -> int {
    opponent_advantage_count(n, r, b) / robot_advantage_count(n, r, b) + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed indexing by casting to usize */
fn exec_robot_advantage_count(n: i8, r: Vec<i8>, b: Vec<i8>) -> (count: i8)
    requires valid_input(n as int, r@.map_values(|x| x as int), b@.map_values(|x| x as int))
    ensures count as int == robot_advantage_count(n as int, r@.map_values(|x| x as int), b@.map_values(|x| x as int))
{
    let mut count = 0;
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            count as int == robot_advantage_count(i as int, r@.map_values(|x| x as int), b@.map_values(|x| x as int)),
        decreases n - i
    {
        if r[i as usize] == 1 && b[i as usize] == 0 {
            count += 1;
        }
        i += 1;
    }
    count
}

/* helper modified by LLM (iteration 5): fixed indexing by casting to usize */
fn exec_opponent_advantage_count(n: i8, r: Vec<i8>, b: Vec<i8>) -> (count: i8)
    requires valid_input(n as int, r@.map_values(|x| x as int), b@.map_values(|x| x as int))
    ensures count as int == opponent_advantage_count(n as int, r@.map_values(|x| x as int), b@.map_values(|x| x as int))
{
    let mut count = 0;
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            count as int == opponent_advantage_count(i as int, r@.map_values(|x| x as int), b@.map_values(|x| x as int)),
        decreases n - i
    {
        if r[i as usize] == 0 && b[i as usize] == 1 {
            count += 1;
        }
        i += 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, r: Vec<i8>, b: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int))
    ensures if can_win(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)) { result as int == min_max_point_value(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)) } else { result == -1 }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed division to use i8 arithmetic */
{
    let robot_count = exec_robot_advantage_count(n, r, b);
    if robot_count == 0 {
        -1
    } else {
        let opponent_count = exec_opponent_advantage_count(n, r, b);
        let quotient = opponent_count / robot_count;
        quotient + 1
    }
}
// </vc-code>


}

fn main() {}