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

proof fn count_robot_advantage(n: int, r: Seq<i8>, b: Seq<i8>) -> (count: int)
    requires
        n > 0,
        r.len() == n,
        b.len() == n,
        (forall|i: int| 0 <= i < n ==> (r[i] == 0i8 || r[i] == 1i8)),
        (forall|i: int| 0 <= i < n ==> (b[i] == 0i8 || b[i] == 1i8)),
    ensures
        count == robot_advantage_count(n, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)),
{
    let mut c: int = 0;
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            c >= 0,
            c == Set::new(|j: int| 0 <= j < i && r[j] == 1i8 && b[j] == 0i8).len() as int,
    {
        if r[i] == 1i8 && b[i] == 0i8 {
            c += 1;
        }
        i += 1;
    }
    c
}

proof fn count_opponent_advantage(n: int, r: Seq<i8>, b: Seq<i8>) -> (count: int)
    requires
        n > 0,
        r.len() == n,
        b.len() == n,
        (forall|i: int| 0 <= i < n ==> (r[i] == 0i8 || r[i] == 1i8)),
        (forall|i: int| 0 <= i < n ==> (b[i] == 0i8 || b[i] == 1i8)),
    ensures
        count == opponent_advantage_count(n, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)),
{
    let mut c: int = 0;
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i <= n,
            c >= 0,
            c == Set::new(|j: int| 0 <= j < i && r[j] == 0i8 && b[j] == 1i8).len() as int,
    {
        if r[i] == 0i8 && b[i] == 1i8 {
            c += 1;
        }
        i += 1;
    }
    c
}

/* helper modified by LLM (iteration 5): Fixed return statements and added ghost conversion helper */
ghost fn to_ghost_int(x: i8) -> int {
    x as int
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, r: Vec<i8>, b: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int))
    ensures if can_win(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)) { result as int == min_max_point_value(n as int, r@.map_values(|x: i8| x as int), b@.map_values(|x: i8| x as int)) } else { result == -1 }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use ghost operations in proof block and fix type conversions */
    proof {
        let ghost_n = n as int;
        let ghost_r = r@.map_values(to_ghost_int);
        let ghost_b = b@.map_values(to_ghost_int);
        
        if !can_win(ghost_n, ghost_r, ghost_b) {
            return -1;
        }
    }
    
    let mut robot_adv: i32 = 0;
    let mut opp_adv: i32 = 0;
    
    let mut i: usize = 0;
    while i < n as usize
        invariant
            i <= n as usize,
            robot_adv >= 0,
            opp_adv >= 0,
            robot_adv == (|| { let mut count = 0; for j in 0..i { if r[j] == 1 && b[j] == 0 { count += 1; } } count })(),
            opp_adv == (|| { let mut count = 0; for j in 0..i { if r[j] == 0 && b[j] == 1 { count += 1; } } count })(),
    {
        if r[i] == 1 && b[i] == 0 {
            robot_adv += 1;
        }
        if r[i] == 0 && b[i] == 1 {
            opp_adv += 1;
        }
        i += 1;
    }
    
    proof {
        assert(robot_adv > 0);
    }
    
    let result = (opp_adv / robot_adv + 1) as i8;
    result
}
// </vc-code>


}

fn main() {}