// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn calculate_ski_time(path: Seq<char>) -> nat
    decreases path.len()
{
    if path.len() == 0 {
        0
    } else {
        5 // Placeholder - actual implementation would track visited segments
    }
}

fn calculate_ski_time_exec(path: Seq<char>) -> (result: nat)
    requires path.len() > 0,
    ensures 
        result > 0,
        result >= path.len(),
        result <= path.len() * 5,
        result == calculate_ski_time(path),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

/* Time should always be positive */
proof fn ski_time_positive(path: Seq<char>)
    requires path.len() > 0,
    ensures calculate_ski_time(path) > 0,
{
    assume(false); // TODO: Remove this line and implement the proof
}

/* Time is at least path length */  
proof fn ski_time_lower_bound(path: Seq<char>)
    requires path.len() > 0,
    ensures calculate_ski_time(path) >= path.len(),
{
    assume(false); // TODO: Remove this line and implement the proof
}

/* Time is at most path length * 5 */
proof fn ski_time_upper_bound(path: Seq<char>)
    requires path.len() > 0,
    ensures calculate_ski_time(path) <= path.len() * 5,
{
    assume(false); // TODO: Remove this line and implement the proof
}

/* Concatenated paths are bounded by sum of individual path times */
proof fn ski_time_composition_bound(path1: Seq<char>, path2: Seq<char>)
    requires path1.len() > 0 && path2.len() > 0,
    ensures calculate_ski_time(path1.add(path2)) <= calculate_ski_time(path1) + calculate_ski_time(path2),
{
    assume(false); // TODO: Remove this line and implement the proof
}

/* Edge cases */
proof fn north_direction_time()
    ensures calculate_ski_time(seq!['N']) == 5,
{
    assume(false); // TODO: Remove this line and implement the proof
}

proof fn north_south_time()
    ensures calculate_ski_time(seq!['N', 'S']) == 6,
{
    assume(false); // TODO: Remove this line and implement the proof
}

/* Apps difficulty: interview */
/* Assurance level: guarded_and_plausible */

}

fn main() {
    // println!("{}", calculate_ski_time_exec(seq!['N', 'N', 'N']));  // Should output: 15
    // println!("{}", calculate_ski_time_exec(seq!['N', 'S']));   // Should output: 6
    // println!("{}", calculate_ski_time_exec(seq!['N', 'W', 'N', 'W', 'S'])); // Should output: 25
}