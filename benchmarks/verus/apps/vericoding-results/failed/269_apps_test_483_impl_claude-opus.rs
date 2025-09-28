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
    /* code modified by LLM (iteration 5): fixed arithmetic overflow and position ordering proof */
    let mut min_time: i8 = -1;
    let mut i: usize = 0;
    
    while i < (n - 1) as usize
        invariant
            n >= 1,
            directions@.len() == n,
            positions@.len() == n,
            i <= (n - 1) as usize,
            valid_input(n as int, directions@, positions@.map(|j: int, v: i8| v as int)),
            min_time == -1 || min_time >= 0,
            min_time != -1 ==> exists|j: int| 0 <= j < i && has_collision_pair(j, directions@) && collision_time(j, positions@.map(|k: int, v: i8| v as int)) == min_time,
            min_time != -1 ==> forall|j: int| 0 <= j < i && has_collision_pair(j, directions@) ==> collision_time(j, positions@.map(|k: int, v: i8| v as int)) >= min_time,
            min_time == -1 ==> forall|j: int| 0 <= j < i ==> !has_collision_pair(j, directions@),
        decreases (n - 1) as usize - i
    {
        if directions[i] == 'R' && directions[i + 1] == 'L' {
            // Calculate time using i8 arithmetic
            let pos0: i8 = positions[i];
            let pos1: i8 = positions[i + 1];
            
            // Prove that pos1 > pos0 before subtraction
            proof {
                assert(valid_input(n as int, directions@, positions@.map(|j: int, v: i8| v as int)));
                assert(0 <= i as int && (i + 1) as int < n);
                let i_int = i as int;
                assert(positions@.map(|j: int, v: i8| v as int)[i_int] < positions@.map(|j: int, v: i8| v as int)[i_int + 1]);
                assert((pos0 as int) == positions@.map(|j: int, v: i8| v as int)[i_int]);
                assert((pos1 as int) == positions@.map(|j: int, v: i8| v as int)[i_int + 1]);
                assert((pos0 as int) < (pos1 as int));
                assert((pos1 as int) - (pos0 as int) >= 0);
                assert((pos1 as int) - (pos0 as int) <= i8::MAX);
            }
            
            let diff: i8 = (pos1 as int - pos0 as int) as i8;
            let time: i8 = diff / 2;
            
            proof {
                assert(time >= 0);
                assert((time as int) == collision_time(i as int, positions@.map(|k: int, v: i8| v as int)));
            }
            
            if min_time == -1 || time < min_time {
                min_time = time;
                proof {
                    assert(min_time >= 0);
                    assert(has_collision_pair(i as int, directions@));
                    assert((min_time as int) == collision_time(i as int, positions@.map(|k: int, v: i8| v as int)));
                }
            }
        }
        proof {
            assert(min_time == -1 || min_time >= 0);
        }
        i = i + 1;
    }
    
    min_time
}
// </vc-code>


}

fn main() {}