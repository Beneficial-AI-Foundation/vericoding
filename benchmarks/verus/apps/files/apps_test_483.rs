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
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}