// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, directions: Seq<char>, positions: Seq<int>) -> bool {
    n >= 1 &&
    directions.len() == n &&
    positions.len() == n &&
    (forall|i: int| 0 <= i < n ==> directions[i] == 'R' || directions[i] == 'L') &&
    (forall|i: int| 0 <= i < n ==> positions[i] % 2 == 0 && positions[i] >= 0) &&
    (forall|i: int, j: int| 0 <= i < j < n ==> positions[i] < positions[j])
}

spec fn has_collision_pair(i: int, directions: Seq<char>) -> bool {
    0 <= i < directions.len()-1 && 
    directions[i] == 'R' && directions[i+1] == 'L'
}

spec fn has_collision(directions: Seq<char>, positions: Seq<int>) -> bool 
    recommends directions.len() == positions.len()
{
    exists|i: int| #[trigger] has_collision_pair(i, directions)
}

spec fn collision_time(i: int, positions: Seq<int>) -> int
    recommends 0 <= i < positions.len()-1
{
    (positions[i+1] - positions[i]) / 2
}

spec fn is_minimal_collision_time(result: int, directions: Seq<char>, positions: Seq<int>) -> bool
    recommends directions.len() == positions.len()
{
    (forall|i: int| has_collision_pair(i, directions) ==> 
        collision_time(i, positions) >= result) &&
    (exists|i: int| #[trigger] has_collision_pair(i, directions) && 
        collision_time(i, positions) == result)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate Vec<char> index to Seq<char> */
proof fn vec_seq_index_char(v: &Vec<char>, i: int)
    requires
        0 <= i,
        i < v.len() as int,
    ensures
        v@[i] == v[i],
{
    assert(v@[i] == v[i]);
}

/* helper modified by LLM (iteration 5): relate Vec<i8> index to Seq<int> converted */
proof fn vec_seq_index_i8_to_int(v: &Vec<i8>, i: int)
    requires
        0 <= i,
        i < v.len() as int,
    ensures
        (v@[i] as int) == (v[i] as int),
{
    assert((v@[i] as int) == (v[i] as int));
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, directions: Vec<char>, positions: Vec<i8>) -> (result: i8)
    requires 
        valid_input(n as int, directions@, positions@.map(|i: int, v: i8| v as int)),
    ensures 
        result == -1 || result >= 0,
        result != -1 ==> has_collision(directions@, positions@.map(|i: int, v: i8| v as int)),
        result == -1 ==> !has_collision(directions@, positions@.map(|i: int, v: i8| v as int)),
        result != -1 ==> is_minimal_collision_time(result as int, directions@, positions@.map(|i: int, v: i8| v as int)),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use usize indices and avoid int casts in executable code, maintain specs in invariants */
{
    let len = directions.len();
    let mut ans: i8 = -1;
    let mut i: usize = 0;

    while i < len - 1
        invariant
            0 <= (i as int),
            (i as int) <= (len as int),
            (ans == -1) == (!exists|j: int| 0 <= j < (i as int) && has_collision_pair(j, directions@)),
            (ans != -1) ==> (forall|j: int| 0 <= j < (i as int) && has_collision_pair(j, directions@) ==> collision_time(j, positions@.map(|k: int, v: i8| v as int) ) >= (ans as int)),
            (ans != -1) ==> (exists|j: int| 0 <= j < (i as int) && has_collision_pair(j, directions@) && collision_time(j, positions@.map(|k: int, v: i8| v as int)) == (ans as int)),
        decreases
            (len as int - i as int)
    {
        let dir_i = directions[i];
        let dir_ip1 = directions[i + 1];
        if dir_i == 'R' && dir_ip1 == 'L' {
            let p_i = positions[i];
            let p_ip1 = positions[i + 1];
            let t = (p_ip1 - p_i) / 2;

            if ans == -1 || t < ans {
                ans = t;
                proof {
                    vec_seq_index_char(&directions, i as int);
                    vec_seq_index_char(&directions, (i as int) + 1);
                    vec_seq_index_i8_to_int(&positions, i as int);
                    vec_seq_index_i8_to_int(&positions, (i as int) + 1);
                }
            }
        }

        i = i + 1;
    }

    proof {
        assert((ans == -1) == (!exists|j: int| 0 <= j < (i as int) && has_collision_pair(j, directions@)));
    }

    let result = ans;
    result
}

// </vc-code>


}

fn main() {}