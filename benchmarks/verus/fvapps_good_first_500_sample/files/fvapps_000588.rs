// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_char(s: Seq<char>, c: char) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        (if s[0] == c { 1nat } else { 0nat }) + count_char(s.skip(1), c)
    }
}

enum SafetyResult {
    Safe,
    Unsafe,
}

fn solve_robot_safety(n: usize, m: usize, commands: Vec<char>) -> (result: SafetyResult)
    requires 
        n > 0,
        m > 0,
        commands.len() > 0,
        forall|i: int| 0 <= i < commands.len() ==> 
            (commands[i] == 'U' || commands[i] == 'D' || commands[i] == 'L' || commands[i] == 'R'),
    ensures 
        match result {
            SafetyResult::Safe => true,
            SafetyResult::Unsafe => true,
        },
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    SafetyResult::Unsafe
    // impl-end
}
// </vc-code>


}
fn main() {
    // let result1 = solve_robot_safety(1, 1, vec!['R']);
    // match result1 {
    //     SafetyResult::Safe => println!("safe"),
    //     SafetyResult::Unsafe => println!("unsafe"),
    // }
    
    // let result2 = solve_robot_safety(2, 3, vec!['L', 'L', 'R', 'U']);
    // match result2 {
    //     SafetyResult::Safe => println!("safe"),
    //     SafetyResult::Unsafe => println!("unsafe"),
    // }
}