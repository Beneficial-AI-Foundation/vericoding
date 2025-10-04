// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn die_simulator_spec(n: usize, roll_max: Seq<usize>) -> usize
{
    0  // placeholder specification
}

fn die_simulator(n: usize, roll_max: Vec<usize>) -> (result: usize)
    requires 
        1 <= n && n <= 20,
        roll_max.len() == 6,
        forall|i: int| 0 <= i < roll_max.len() ==> 1 <= roll_max[i] && roll_max[i] <= 15,
    ensures 
        0 <= result && result < 1000000007,
        result == die_simulator_spec(n, roll_max@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


proof fn die_simulator_within_bounds(n: usize, roll_max: Vec<usize>)
    requires 
        1 <= n && n <= 20,
        roll_max.len() == 6,
        forall|i: int| 0 <= i < roll_max.len() ==> 1 <= roll_max[i] && roll_max[i] <= 15,
    ensures ({
        let result = die_simulator_spec(n, roll_max@);
        0 <= result && result < 1000000007
    })
{
    assume(false); /* TODO: Remove this line and implement the proof */
}

proof fn die_simulator_base_case(roll_max: Vec<usize>)
    requires 
        roll_max.len() == 6,
        forall|i: int| 0 <= i < roll_max.len() ==> 1 <= roll_max[i] && roll_max[i] <= 15,
    ensures 
        die_simulator_spec(1, roll_max@) == 6,
{
    assume(false); /* TODO: Remove this line and implement the proof */
}

proof fn die_simulator_monotonic(n: usize, strict: Vec<usize>, loose: Vec<usize>)
    requires 
        strict.len() == 6,
        loose.len() == 6,
        forall|i: int| 0 <= i < strict.len() ==> strict[i] == 1,
        forall|i: int| 0 <= i < loose.len() ==> loose[i] == 15,
    ensures 
        die_simulator_spec(n, strict@) <= die_simulator_spec(n, loose@),
{
    assume(false); /* TODO: Remove this line and implement the proof */
}

}

fn main() {
    // Apps difficulty: interview
    // Assurance level: guarded

    // #guard_msgs in
    // #eval dieSimulator 2 [1, 1, 2, 2, 2, 3]
    // Expected: 34

    // #guard_msgs in  
    // #eval dieSimulator 2 [1, 1, 1, 1, 1, 1]
    // Expected: 30

    // #guard_msgs in
    // #eval dieSimulator 3 [1, 1, 1, 2, 2, 3]
    // Expected: 181
}