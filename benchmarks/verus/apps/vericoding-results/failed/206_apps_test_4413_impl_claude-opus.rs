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
{
    /* code modified by LLM (iteration 5): fixed syntax error in invariant by properly parenthesizing complex boolean expression */
    let n = skills.len();
    let mut found_adjacent = false;
    let mut i: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            found_adjacent <==> exists|p: int, q: int| 
                0 <= p < q < i as int && 
                (skills@.map(|idx, x| x as int)[p] - skills@.map(|idx, x| x as int)[q] == 1 || 
                 skills@.map(|idx, x| x as int)[q] - skills@.map(|idx, x| x as int)[p] == 1),
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                i < j <= n,
                0 <= i < n,
                found_adjacent <==> exists|p: int, q: int| 
                    ((0 <= p < q < i as int) || (p == i as int && i as int < q < j as int)) && 
                    (skills@.map(|idx, x| x as int)[p] - skills@.map(|idx, x| x as int)[q] == 1 || 
                     skills@.map(|idx, x| x as int)[q] - skills@.map(|idx, x| x as int)[p] == 1),
            decreases n - j
        {
            let diff = if skills[i] >= skills[j] {
                skills[i] - skills[j]
            } else {
                skills[j] - skills[i]
            };
            
            if diff == 1 {
                found_adjacent = true;
                assert(skills@.map(|idx, x| x as int)[i as int] - skills@.map(|idx, x| x as int)[j as int] == 1 ||
                       skills@.map(|idx, x| x as int)[j as int] - skills@.map(|idx, x| x as int)[i as int] == 1);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    if found_adjacent {
        assert(has_adjacent_skills(skills@.map(|idx, x| x as int)));
        2
    } else {
        assert(!has_adjacent_skills(skills@.map(|idx, x| x as int)));
        1
    }
}
// </vc-code>


}

fn main() {}