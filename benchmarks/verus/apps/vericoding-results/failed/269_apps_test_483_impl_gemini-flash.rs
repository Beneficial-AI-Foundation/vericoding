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
    let n_int: int = n as int;
    let directions_seq = directions@;
    let positions_seq = positions@.map(|idx: int, v: i8| v as int);

    if !has_collision(directions_seq, positions_seq) {
        return -1;
    }

    let mut min_t: i8 = 127; // Max value of i8, used as an initial upper bound

    let mut i: int = 0;
    while i < n_int - 1
        invariant
            0 <= i && i <= n_int - 1,
            n_int == directions_seq.len(),
            n_int == positions_seq.len(),
            min_t >= 0 && min_t <= 127,
            // Property 1: For all considered collision pairs `j`, their collision time
            // must be greater than or equal to `min_t` if `min_t` is not the initial max value
            (!exists|j: int| 0 <= j < i && has_collision_pair(j, directions_seq)) ||
            (forall |j: int| 0 <= j < i && has_collision_pair(j, directions_seq) ==> (collision_time(j, positions_seq) as i8) >= min_t),
            // Property 2: If `min_t` is not the initial max value, there must exist at least one
            // collision pair `j` among those considered whose collision time equals `min_t`
            (min_t == 127) ||
            (exists |j: int| 0 <= j < i && has_collision_pair(j, directions_seq) && (collision_time(j, positions_seq) as i8) == min_t),
        decreases n_int - 1 - i
    {
        if directions_seq[i] == 'R' && directions_seq[i + 1] == 'L' {
            let time = (positions_seq[i + 1] - positions_seq[i]) / 2;
            if (time as i8) < min_t {
                min_t = time as i8;
            }
        }
        i = i + 1;
    }

    min_t
}
// </vc-code>


}

fn main() {}