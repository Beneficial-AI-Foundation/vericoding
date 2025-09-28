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
/* helper modified by LLM (iteration 2): added prefix count spec function for robot advantage */
spec fn robot_advantage_count_prefix(i: int, r: Seq<int>, b: Seq<int>) -> int {
    Set::new(|j: int| 0 <= j < i && r[j] == 1 && b[j] == 0).len() as int
}

/* helper modified by LLM (iteration 2): added prefix count spec function for opponent advantage */
spec fn opponent_advantage_count_prefix(i: int, r: Seq<int>, b: Seq<int>) -> int {
    Set::new(|j: int| 0 <= j < i && r[j] == 0 && b[j] == 1).len() as int
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, r: Vec<i8>, b: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int))
    ensures if can_win(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)) { result as int == min_max_point_value(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)) } else { result == -1 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [fixed compilation error: changed 'ghost let' to 'let ghost'] */
    let ghost r_seq = r@.map_values(|x: i8| x as int);
    let ghost b_seq = b@.map_values(|x: i8| x as int);

    let mut robot_adv: i8 = 0;
    let mut opponent_adv: i8 = 0;
    let mut i: i8 = 0;

    while i < n
        invariant
            0 <= i <= n,
            robot_adv as int == robot_advantage_count_prefix(i as int, r_seq, b_seq),
            opponent_adv as int == opponent_advantage_count_prefix(i as int, r_seq, b_seq),
        decreases n - i
    {
        if r[i as usize] == 1 && b[i as usize] == 0 {
            robot_adv = robot_adv + 1;
        }
        if r[i as usize] == 0 && b[i as usize] == 1 {
            opponent_adv = opponent_adv + 1;
        }
        i = i + 1;
    }

    if robot_adv > 0 {
        (opponent_adv / robot_adv) + 1
    } else {
        -1
    }
}
// </vc-code>


}

fn main() {}