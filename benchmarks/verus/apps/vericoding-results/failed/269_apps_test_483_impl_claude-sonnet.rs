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
/* helper modified by LLM (iteration 5): Fixed lemma proofs and added proper lemma_specific_collision */
proof fn lemma_collision_pair_bounds(i: int, directions: Seq<char>)
    requires has_collision_pair(i, directions)
    ensures 0 <= i < directions.len() - 1
{
}

proof fn lemma_collision_time_positive(i: int, positions: Seq<int>)
    requires 
        0 <= i < positions.len() - 1,
        positions[i] % 2 == 0,
        positions[i+1] % 2 == 0,
        positions[i] < positions[i+1]
    ensures collision_time(i, positions) > 0
{
    assert(positions[i+1] - positions[i] >= 2);
    assert((positions[i+1] - positions[i]) / 2 >= 1);
}

proof fn lemma_minimal_collision_exists(directions: Seq<char>, positions: Seq<int>)
    requires 
        directions.len() == positions.len(),
        directions.len() >= 1,
        has_collision(directions, positions)
    ensures exists|result: int| is_minimal_collision_time(result, directions, positions)
{
    proof {
        let witness_i = choose|i: int| has_collision_pair(i, directions);
        let witness_time = collision_time(witness_i, positions);
        assert(has_collision_pair(witness_i, directions));
        assert(collision_time(witness_i, positions) == witness_time);
        
        let min_time = choose|t: int| 
            (exists|j: int| has_collision_pair(j, directions) && collision_time(j, positions) == t) &&
            (forall|j: int| has_collision_pair(j, directions) ==> collision_time(j, positions) >= t);
        
        assert(is_minimal_collision_time(min_time, directions, positions));
    }
}

proof fn lemma_specific_collision(i: int, directions: Seq<char>, positions: Seq<int>)
    requires
        0 <= i < directions.len() - 1,
        directions[i] == 'R',
        directions[i+1] == 'L'
    ensures
        has_collision_pair(i, directions),
        has_collision(directions, positions)
{
    assert(has_collision_pair(i, directions));
    assert(exists|j: int| #[trigger] has_collision_pair(j, directions));
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
    /* code modified by LLM (iteration 5): Fixed arithmetic overflow and postcondition */
    let mut min_time: i8 = -1;
    let mut found_collision = false;
    
    let mut i = 0;
    while i < n - 1
        invariant
            0 <= i <= n - 1,
            n == directions.len(),
            n == positions.len(),
            found_collision ==> min_time >= 0,
            !found_collision ==> min_time == -1,
            found_collision ==> (exists|j: int| 0 <= j < i && has_collision_pair(j, directions@)),
            !found_collision ==> (forall|j: int| 0 <= j < i ==> !has_collision_pair(j, directions@)),
            found_collision ==> (forall|j: int| 0 <= j < i && has_collision_pair(j, directions@) ==> collision_time(j, positions@.map(|k: int, v: i8| v as int)) >= min_time as int),
            found_collision ==> (exists|j: int| 0 <= j < i && has_collision_pair(j, directions@) && collision_time(j, positions@.map(|k: int, v: i8| v as int)) == min_time as int)
        decreases n - 1 - i
    {
        if directions[i as usize] == 'R' && directions[(i + 1) as usize] == 'L' {
            assert(positions[(i + 1) as usize] > positions[i as usize]);
            assert((positions[(i + 1) as usize] - positions[i as usize]) >= 0);
            assert((positions[(i + 1) as usize] - positions[i as usize]) / 2 >= 0);
            
            let time = (positions[(i + 1) as usize] - positions[i as usize]) / 2;
            
            lemma_specific_collision(i as int, directions@, positions@.map(|k: int, v: i8| v as int));
            
            if !found_collision || time < min_time {
                min_time = time;
                found_collision = true;
            }
        }
        i += 1;
    }
    
    if found_collision {
        assert(exists|j: int| 0 <= j < n - 1 && has_collision_pair(j, directions@));
        assert(has_collision(directions@, positions@.map(|k: int, v: i8| v as int)));
        assert(is_minimal_collision_time(min_time as int, directions@, positions@.map(|k: int, v: i8| v as int)));
    } else {
        assert(forall|j: int| 0 <= j < n - 1 ==> !has_collision_pair(j, directions@));
        assert(!has_collision(directions@, positions@.map(|k: int, v: i8| v as int)));
    }
    
    min_time
}
// </vc-code>


}

fn main() {}