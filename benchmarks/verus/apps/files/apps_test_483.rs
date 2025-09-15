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

spec fn has_collision(directions: Seq<char>, positions: Seq<int>) -> bool
    recommends
        directions.len() == positions.len()
{
    exists|i: int| 0 <= i < directions.len()-1 && directions[i] == 'R' && directions[i+1] == 'L'
}

spec fn collision_time(i: int, positions: Seq<int>) -> int
    recommends
        0 <= i < positions.len()-1
{
    (positions[i+1] - positions[i]) / 2
}

spec fn is_minimal_collision_time(result: int, directions: Seq<char>, positions: Seq<int>) -> bool
    recommends
        directions.len() == positions.len()
{
    (forall|i: int| 0 <= i < directions.len()-1 && directions[i] == 'R' && directions[i+1] == 'L' ==> 
        collision_time(i, positions) >= result) &&
    (exists|i: int| 0 <= i < directions.len()-1 && directions[i] == 'R' && directions[i+1] == 'L' && 
        collision_time(i, positions) == result)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, directions: Seq<char>, positions: Seq<int>) -> (result: int)
    requires 
        valid_input(n, directions, positions)
    ensures 
        result == -1 || result >= 0,
        result != -1 ==> has_collision(directions, positions),
        result == -1 ==> !has_collision(directions, positions),
        result != -1 ==> is_minimal_collision_time(result, directions, positions)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}