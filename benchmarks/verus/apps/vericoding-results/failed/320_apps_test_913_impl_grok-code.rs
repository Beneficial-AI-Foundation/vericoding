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
/* helper modified by LLM (iteration 2): Fixed forall syntax by adding proper triggers and corrected index access in body. */
fn helper_robot_advantage(vec_r: Vec<i8>, vec_b: Vec<i8>, n: int, i: int) -> int
    requires
        i <= n,
        vec_r@.len() == n,
        vec_b@.len() == n,
        forall |j: int| #![trigger] (vec_r@[j]) ==> 0 <= j < n && (vec_r@[j] == 0 || vec_r@[j] == 1),
        forall |j: int| #![trigger] (vec_b@[j]) ==> 0 <= j < n && (vec_b@[j] == 0 || vec_b@[j] == 1),
    ensures
        result == Set::new(|j: int| 0 <= j < i && vec_r@[j] == 1 && vec_b@[j] == 0).len() as int,
{
    if i == 0 { return 0; }
    let prev = helper_robot_advantage(vec_r, vec_b, n, i - 1);
    if vec_r@[i-1] == 1 && vec_b@[i-1] == 0 {
        return prev + 1;
    } else {
        return prev;
    }
}

/* helper modified by LLM (iteration 2): Fixed forall syntax by adding proper triggers and corrected index access in body. */
fn helper_opponent_advantage(vec_r: Vec<i8>, vec_b: Vec<i8>, n: int, i: int) -> int
    requires
        i <= n,
        vec_r@.len() == n,
        vec_b@.len() == n,
        forall |j: int| #![trigger] (vec_r@[j]) ==> 0 <= j < n && (vec_r@[j] == 0 || vec_r@[j] == 1),
        forall |j: int| #![trigger] (vec_b@[j]) ==> 0 <= j < n && (vec_b@[j] == 0 || vec_b@[j] == 1),
    ensures
        result == Set::new(|j: int| 0 <= j < i && vec_r@[j] == 0 && vec_b@[j] == 1).len() as int,
{
    if i == 0 { return 0; }
    let prev = helper_opponent_advantage(vec_r, vec_b, n, i - 1);
    if vec_r@[i-1] == 0 && vec_b@[i-1] == 1 {
        return prev + 1;
    } else {
        return prev;
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, r: Vec<i8>, b: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int))
    ensures if can_win(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)) { result as int == min_max_point_value(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)) } else { result == -1 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Implemented main logic using helper functions to compute advantage counts and determine result. */
    let n_int = n as int;
    let robot_adv = helper_robot_advantage(r, b, n_int, n_int);
    let oppo_adv = helper_opponent_advantage(r, b, n_int, n_int);
    if robot_adv > 0 {
        let point = oppo_adv / robot_adv + 1;
        point as i8
    } else {
        -1
    }
}
// </vc-code>


}

fn main() {}