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

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, r: Vec<i8>, b: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int))
    ensures if can_win(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)) { result as int == min_max_point_value(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)) } else { result == -1 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut robot_wins: i8 = 0;
    let mut opponent_wins: i8 = 0;
    let mut i: usize = 0;
    
    while i < n as usize
        invariant
            0 <= i <= n as usize,
            r.len() == n as usize,
            b.len() == n as usize,
            robot_wins as int == Set::new(|j: int| 0 <= j < i as int && r@[j] as int == 1 && b@[j] as int == 0).len() as int,
            opponent_wins as int == Set::new(|j: int| 0 <= j < i as int && r@[j] as int == 0 && b@[j] as int == 1).len() as int,
        decreases n as usize - i
    {
        if r[i] == 1 && b[i] == 0 {
            robot_wins = robot_wins + 1;
        } else if r[i] == 0 && b[i] == 1 {
            opponent_wins = opponent_wins + 1;
        }
        i = i + 1;
    }
    
    if robot_wins > 0 {
        let result = opponent_wins / robot_wins + 1;
        result
    } else {
        -1
    }
}
// </vc-code>


}

fn main() {}