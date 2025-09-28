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
/* helper modified by LLM (iteration 5): convert Vec<i8> to Seq<int> */
spec fn seq_of_vec(skills: Vec<i8>) -> Seq<int> {
    skills@.map(|i, x| x as int)
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
    /* code modified by LLM (iteration 5): iterate pairs to find adjacent skills using ghost sequence */
    let ghost s: Seq<int> = seq_of_vec(skills);
    let ghost n: int = skills.len() as int;
    let mut a: int = 0;
    let mut found: bool = false;

    while a < n && !found
        invariant
            0 <= a && a <= n,
            (!found) ==> forall|i: int, j: int| 0 <= i < j < a ==> !((s@[i] - s@[j] == 1) || (s@[j] - s@[i] == 1)),
        decreases n - a
    {
        let mut b: int = a + 1;
        while b < n && !found
            invariant
                0 <= a && a <= n,
                0 <= b && b <= n,
                (!found) ==> forall|i: int, j: int| ((0 <= i && i < j && j < a) || (i == a && a < j && j < b)) ==> !((s@[i] - s@[j] == 1) || (s@[j] - s@[i] == 1)),
            decreases n - b
        {
            if (s@[a] - s@[b] == 1) || (s@[b] - s@[a] == 1) {
                found = true;
            } else {
                b = b + 1;
            }
        }

        if !found {
            a = a + 1;
        }
    }

    (if found { 2 } else { 1 }) as i8
}

// </vc-code>


}

fn main() {}