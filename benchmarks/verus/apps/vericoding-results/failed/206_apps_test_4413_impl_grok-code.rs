// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(skills: Seq<int>) -> bool {
    skills.len() >= 0
}

spec fn has_adjacent_skills(skills: Seq<int>) -> bool {
    exists|i: int, j: int| 0 <= i < j < skills.len() && (skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(skills: Vec<i8>) -> (teams: i8)
    requires 
        valid_input(skills@.map(|i, x| x as int))
    ensures 
        teams == 1 || teams == 2,
        teams == 2 <==> has_adjacent_skills(skills@.map(|i, x| x as int)),
        teams == 1 <==> !has_adjacent_skills(skills@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Implement nested loops to check all pairs for adjacent skills differing by 1 */
{
    let mut has_adj: bool = false;
    let mut ii: usize = 0;
    while ii < skills.len() && !has_adj
    {
        let si = skills@[ii] as int;
        let mut jj = ii + 1;
        while jj < skills.len()
        {
            let sj = skills@[jj] as int;
            if si - sj == 1 || sj - si == 1 {
                has_adj = true;
            }
            jj += 1;
        }
        ii += 1;
    }
    if has_adj {
        2i8
    } else {
        1i8
    }
}
// </vc-code>


}

fn main() {}