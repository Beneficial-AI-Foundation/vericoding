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
{
    /* code modified by LLM (iteration 5): use usize for loop index and refine invariants */
    let ghost pos_int = positions@.map(|_idx: int, v: i8| v as int);
    let mut min_time: i8 = -1;
    let n_usize = n as usize;

    if n_usize < 2 {
        assert(!has_collision(directions@, pos_int)) by {
            assert forall |i: int| !has_collision_pair(i, directions@) by {
                if has_collision_pair(i, directions@) {
                    assert(i + 1 < directions@.len());
                    assert(directions@.len() < 2);
                    assert(i + 1 < 2);
                    assert(i < 1);
                    assert(i == 0);
                    assert(1 < directions@.len());
                    assert(false);
                }
            }
        };
        return -1;
    }

    let mut i: usize = 0;
    while i < n_usize - 1
        invariant
            valid_input(n as int, directions@, pos_int),
            n_usize >= 2,
            0 <= i <= n_usize - 1,
            (exists|j: int| 0 <= j < i as int && #[trigger] has_collision_pair(j, directions@)) <==> (min_time != -1),
            min_time != -1 ==> (
                (exists|k: int| 0 <= k < i as int && #[trigger] has_collision_pair(k, directions@) &&
                    collision_time(k, pos_int) == min_time as int)
            ),
            min_time != -1 ==> (
                (forall|k: int| 0 <= k < i as int && has_collision_pair(k, directions@) ==> 
                    collision_time(k, pos_int) >= min_time as int)
            ),
        decreases (n_usize - 1) - i
    {
        if directions[i] == 'R' && directions[i + 1] == 'L' {
            let time = (positions[i + 1] - positions[i]) / 2;

            if min_time == -1 || time < min_time {
                min_time = time;
            }
        }
        i = i + 1;
    }

    min_time
}
// </vc-code>


}

fn main() {}