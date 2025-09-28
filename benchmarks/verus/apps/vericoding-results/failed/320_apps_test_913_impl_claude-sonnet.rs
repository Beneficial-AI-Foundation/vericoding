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
/* helper modified by LLM (iteration 5): fixed types to avoid int/nat in executable code */
proof fn lemma_advantage_counts_bounded(n: int, r: Seq<int>, b: Seq<int>)
    requires valid_input(n, r, b)
    ensures
        0 <= robot_advantage_count(n, r, b) <= n,
        0 <= opponent_advantage_count(n, r, b) <= n
{
    proof {
        assert(Set::new(|i: int| 0 <= i < n && r[i] == 1 && b[i] == 0).subset_of(Set::new(|i: int| 0 <= i < n)));
        assert(Set::new(|i: int| 0 <= i < n && r[i] == 0 && b[i] == 1).subset_of(Set::new(|i: int| 0 <= i < n)));
    }
}

proof fn lemma_division_property(a: int, b: int)
    requires a >= 0, b > 0
    ensures a / b + 1 >= 1
{
}

fn count_robot_advantages(n: i8, r: &Vec<i8>, b: &Vec<i8>) -> (count: i8)
    requires
        valid_input(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)),
        n < 100
    ensures
        count as int == robot_advantage_count(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)),
        0 <= count <= n
{
    let mut count = 0i8;
    let mut i = 0i8;
    while i < n
        invariant
            0 <= i <= n,
            count as int == robot_advantage_count(i as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)),
            0 <= count <= i,
            i < r@.len(),
            i < b@.len()
        decreases n - i
    {
        if r@[i as usize] == 1 && b@[i as usize] == 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}

fn count_opponent_advantages(n: i8, r: &Vec<i8>, b: &Vec<i8>) -> (count: i8)
    requires
        valid_input(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)),
        n < 100
    ensures
        count as int == opponent_advantage_count(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)),
        0 <= count <= n
{
    let mut count = 0i8;
    let mut i = 0i8;
    while i < n
        invariant
            0 <= i <= n,
            count as int == opponent_advantage_count(i as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)),
            0 <= count <= i,
            i < r@.len(),
            i < b@.len()
        decreases n - i
    {
        if r@[i as usize] == 0 && b@[i as usize] == 1 {
            count = count + 1;
        }
        i = i + 1;
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
{
    /* code modified by LLM (iteration 5): used usize for array indexing */
    let robot_count = count_robot_advantages(n, &r, &b);
    
    if robot_count == 0 {
        return -1;
    }
    
    let opponent_count = count_opponent_advantages(n, &r, &b);
    
    proof {
        lemma_advantage_counts_bounded(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int));
        lemma_division_property(opponent_count as int, robot_count as int);
    }
    
    let result = (opponent_count as i8) / (robot_count as i8) + 1;
    result
}
// </vc-code>


}

fn main() {}