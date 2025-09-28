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
/* helper modified by LLM (iteration 4): convert Vec<i8> to Seq<int> */
spec fn seq_of_vec(v: Vec<i8>) -> Seq<int> { v@.map_values(|x: i8| x as int) }

/* helper modified by LLM (iteration 4): prove Vec length matches Seq length */
proof fn vec_len_matches_seq_len(v: Vec<i8>)
    ensures
        v.len() as int == seq_of_vec(v).len(),
{
    proof {
        assert(seq_of_vec(v).len() == v.len() as int);
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
    /* code modified by LLM (iteration 4): replaced ghost blocks with `let ghost` declarations and proved counts */
    let n_usize: usize = n as usize;
    let ghost n_int: int = n as int;
    let ghost seq_r: Seq<int> = r@.map_values(|x: i8| x as int);
    let ghost seq_b: Seq<int> = b@.map_values(|x: i8| x as int);

    let mut i: usize = 0;
    let mut rcu: usize = 0;
    let mut bcu: usize = 0;
    let ghost mut gi: int = 0;
    let ghost mut rc: int = 0;
    let ghost mut bc: int = 0;

    while i < n_usize
        invariant
            0 <= gi && gi <= n_int,
            gi == i as int,
            rc == Set::new(|j: int| 0 <= j < gi && seq_r[j] == 1 && seq_b[j] == 0).len() as int,
            bc == Set::new(|j: int| 0 <= j < gi && seq_r[j] == 0 && seq_b[j] == 1).len() as int,
        decreases n_int - gi
    {
        let rv: i8 = r[i];
        let bv: i8 = b[i];
        if rv == 1 && bv == 0 {
            rcu = rcu + 1;
            rc = rc + 1;
        } else if rv == 0 && bv == 1 {
            bcu = bcu + 1;
            bc = bc + 1;
        }
        i = i + 1;
        gi = gi + 1;
    }

    if rcu == 0 {
        -1 as i8
    } else {
        let val_usize: usize = bcu / rcu + 1;
        let val_i8: i8 = val_usize as i8;
        proof {
            assert(gi == n_int);
            assert(rc == Set::new(|j: int| 0 <= j < n_int && seq_r[j] == 1 && seq_b[j] == 0).len() as int);
            assert(bc == Set::new(|j: int| 0 <= j < n_int && seq_r[j] == 0 && seq_b[j] == 1).len() as int);
            assert(rc != 0);
            assert(rc == rcu as int);
            assert(bc == bcu as int);
            assert((val_usize as int) == bc / rc + 1);
        }
        val_i8
    }
}

// </vc-code>


}

fn main() {}