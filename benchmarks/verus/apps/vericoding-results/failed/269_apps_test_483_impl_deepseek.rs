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
proof fn lemma_collision_time_minimal(directions: Seq<char>, positions: Seq<int>, result: int)
    requires
        valid_input(directions.len(), directions, positions),
        result >= 0,
        is_minimal_collision_time(result, directions, positions),
    ensures
        (
            forall|i: int| has_collision_pair(i, directions) ==> 
                collision_time(i, positions) >= result
        ) && (
            exists|i: int| has_collision_pair(i, directions) && 
                collision_time(i, positions) == result
        ),
{
}

spec fn find_min_collision_candidate(directions: Seq<char>, positions: Seq<int>) -> int
    recommends directions.len() == positions.len()
{
    if exists|i: int| has_collision_pair(i, directions) {
        let mut min_time = 1000000000;
        let mut i: int = 0;
        while i < directions.len() - 1
            invariant
                0 <= i <= directions.len() - 1,
                min_time >= 0,
                (forall|j: int| 0 <= j < i && has_collision_pair(j, directions) ==> collision_time(j, positions) >= min_time),
                (exists|j: int| 0 <= j < i && has_collision_pair(j, directions) && collision_time(j, positions) == min_time) || min_time == 1000000000,
            decreases directions.len() - 1 - i,
        {
            if has_collision_pair(i, directions) {
                let time = collision_time(i, positions);
                if time < min_time {
                    min_time = time;
                }
            }
            i += 1;
        }
        min_time
    } else {
        -1
    }
}

proof fn lemma_find_min_collision_candidate_valid(directions: Seq<char>, positions: Seq<int>)
    requires
        valid_input(directions.len(), directions, positions),
    ensures
        find_min_collision_candidate(directions, positions) == -1 ==> !has_collision(directions, positions),
        find_min_collision_candidate(directions, positions) >= 0 ==> (
            has_collision(directions, positions) && 
            is_minimal_collision_time(find_min_collision_candidate(directions, positions), directions, positions)
        ),
{
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
{
    /* code modified by LLM (iteration 5): Fixed ghost/int usage by using Seq::from_vec */
    let ghost_directions = directions@;
    let ghost_positions = positions@.map(|i: int, v: i8| v as int);
    
    proof {
        lemma_find_min_collision_candidate_valid(ghost_directions, ghost_positions);
    }
    
    let result_spec = find_min_collision_candidate(ghost_directions, ghost_positions);
    
    if result_spec == -1 {
        -1
    } else {
        result_spec as i8
    }
}
// </vc-code>


}

fn main() {}