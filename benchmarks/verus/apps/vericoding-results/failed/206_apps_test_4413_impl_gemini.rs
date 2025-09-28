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
/* helper modified by LLM (iteration 2): fixed type error in invariant by casting usize to int */
fn has_adjacent_skills_exec(skills: &Vec<i8>) -> (result: bool)
    requires
        valid_input(skills@.map(|i, x| x as int)),
    ensures
        result == has_adjacent_skills(skills@.map(|i, x| x as int)),
{
    let ghost skills_spec = skills@.map(|i, x| x as int);
    let mut i: usize = 0;
    while i < skills.len()
        invariant
            0 <= i <= skills.len(),
            forall|k: int, l: int|
                0 <= k < i && k < l < skills_spec.len() ==>
                    !(skills_spec[k] - skills_spec[l] == 1 || skills_spec[l] - skills_spec[k] == 1),
        decreases skills.len() - i,
    {
        let mut j: usize = i + 1;
        while j < skills.len()
            invariant
                0 <= i < skills.len(),
                i + 1 <= j <= skills.len(),
                forall|k: int, l: int|
                    0 <= k < i && k < l < skills_spec.len() ==>
                        !(skills_spec[k] - skills_spec[l] == 1 || skills_spec[l] - skills_spec[k] == 1),
                forall|l: int|
                    i < l < j ==>
                        !(skills_spec[i as int] - skills_spec[l] == 1 || skills_spec[l] - skills_spec[i as int] == 1),
            decreases skills.len() - j,
        {
            if (skills[i] as i32 - skills[j] as i32 == 1) || (skills[j] as i32 - skills[i] as i32 == 1) {
                assert(has_adjacent_skills(skills_spec));
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    assert(!has_adjacent_skills(skills_spec));
    false
}
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
{
    /* code modified by LLM (iteration 2): calling helper to implement logic */
    if has_adjacent_skills_exec(&skills) {
        2
    } else {
        1
    }
}
// </vc-code>


}

fn main() {}