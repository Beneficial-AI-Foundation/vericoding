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
proof fn adjacent_skills_decidable(skills: Seq<int>)
    ensures
        has_adjacent_skills(skills) || !has_adjacent_skills(skills)
{
}

proof fn check_adjacent_pair(skills: Seq<int>, i: int, j: int)
    requires
        0 <= i < j < skills.len(),
        skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1
    ensures
        has_adjacent_skills(skills)
{
    assert(exists|a: int, b: int| 0 <= a < b < skills.len() && (skills[a] - skills[b] == 1 || skills[b] - skills[a] == 1)) by {
        assert(0 <= i < j < skills.len() && (skills[i] - skills[j] == 1 || skills[j] - skills[i] == 1));
    }
}

/* helper modified by LLM (iteration 5): added lemma to maintain invariant preservation */
proof fn preserve_no_adjacent_skills(skills: Seq<int>, i: int, j: int)
    requires
        0 <= i < j < skills.len(),
        !has_adjacent_skills(skills.subrange(0, i)),
        forall|k: int| i < k < j ==> !((skills[i] - skills[k] == 1) || (skills[k] - skills[i] == 1)),
        !((skills[i] - skills[j] == 1) || (skills[j] - skills[i] == 1))
    ensures
        !has_adjacent_skills(skills.subrange(0, i))
{
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
    /* code modified by LLM (iteration 5): moved skill mapping into spec code to avoid ghost type error */
    let mut i = 0;
    
    while i < skills.len()
        invariant
            0 <= i <= skills.len(),
            forall|a: int, b: int| 0 <= a < b < i ==> !((skills@[a] as int - skills@[b] as int == 1) || (skills@[b] as int - skills@[a] as int == 1))
        decreases skills.len() - i
    {
        let mut j = i + 1;
        while j < skills.len()
            invariant
                i < skills.len(),
                i + 1 <= j <= skills.len(),
                forall|a: int, b: int| 0 <= a < b < i ==> !((skills@[a] as int - skills@[b] as int == 1) || (skills@[b] as int - skills@[a] as int == 1)),
                forall|k: int| i < k < j ==> !((skills@[i as int] as int - skills@[k] as int == 1) || (skills@[k] as int - skills@[i as int] as int == 1))
            decreases skills.len() - j
        {
            let diff = (skills[i] as i16) - (skills[j] as i16);
            if diff == 1 || diff == -1 {
                proof {
                    let skill_seq = skills@.map(|k, x| x as int);
                    check_adjacent_pair(skill_seq, i as int, j as int);
                }
                return 2;
            }
            j += 1;
        }
        i += 1;
    }
    
    proof {
        let skill_seq = skills@.map(|k, x| x as int);
        assert(forall|a: int, b: int| 0 <= a < b < skill_seq.len() ==> !((skill_seq[a] - skill_seq[b] == 1) || (skill_seq[b] - skill_seq[a] == 1)));
        assert(!has_adjacent_skills(skill_seq));
    }
    1
}
// </vc-code>


}

fn main() {}