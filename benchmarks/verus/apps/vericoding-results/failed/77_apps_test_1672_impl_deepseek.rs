// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(magnets: Seq<Seq<char>>) -> bool {
    forall|i: int| 0 <= i < magnets.len() ==> 
        (magnets[i].len() == 2 && 
         ((magnets[i][0] == '0' && magnets[i][1] == '1') || 
          (magnets[i][0] == '1' && magnets[i][1] == '0')))
}

spec fn count_groups(magnets: Seq<Seq<char>>) -> int {
    if magnets.len() == 0 { 
        0 as int
    } else { 
        1 + (Set::new(|i: int| 1 <= i < magnets.len() && magnets[i] != magnets[i-1]).len() as int)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove Vec comparison, use sequence comparison instead */
fn count_groups_executable(magnets: &Vec<Vec<char>>) -> usize 
    requires 
        valid_input(magnets@.map(|i, v: Vec<char>| v@))
    ensures 
        result == count_groups(magnets@.map(|i, v: Vec<char>| v@)) as usize
{
    if magnets.len() == 0 {
        return 0;
    }
    
    let mut groups = 1;
    let ghost seq = magnets@.map(|i, v: Vec<char>| v@);
    
    proof {
        count_groups_matches_spec(seq);
    }
    
    for i in 1..magnets.len() 
        invariant 
            groups >= 1,
            groups <= i + 1,
            groups == 1 + (Set::new(|j: int| 1 <= j < i && seq[j] != seq[j-1]).len() as usize)
        decreases 
            magnets.len() - i
    {
        let prev = magnets[i-1]@;
        let current = magnets[i]@;
        if prev != current {
            groups += 1;
        }
    }
    groups
}

proof fn count_groups_matches_spec(magnets: Seq<Seq<char>>)
    requires
        valid_input(magnets)
    ensures
        count_groups(magnets) == (if magnets.len() == 0 { 0 } else {
            1 + (Set::new(|j: int| 1 <= j < magnets.len() && magnets[j] != magnets[j-1]).len() as int)
        })
{
}
// </vc-helpers>

// <vc-spec>
fn solve(magnets: Vec<Vec<char>>) -> (result: usize)
    requires 
        valid_input(magnets@.map(|i, v: Vec<char>| v@))
    ensures 
        result >= 0,
        magnets@.len() == 0 ==> result == 0,
        magnets@.len() > 0 ==> result >= 1,
        result <= magnets@.len(),
        valid_input(magnets@.map(|i, v: Vec<char>| v@)) ==> result == count_groups(magnets@.map(|i, v: Vec<char>| v@)) as usize
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Call verified helper function */
{
    count_groups_executable(&magnets)
}
// </vc-code>


}

fn main() {}