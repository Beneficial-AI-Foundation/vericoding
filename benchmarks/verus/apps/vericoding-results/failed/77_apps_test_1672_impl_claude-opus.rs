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
/* helper modified by LLM (iteration 4): Added helper to compare magnet configurations with proper preconditions */
fn magnets_equal(m1: &Vec<char>, m2: &Vec<char>) -> (result: bool)
    requires
        m1@.len() == 2,
        m2@.len() == 2
    ensures
        result == (m1@[0] == m2@[0] && m1@[1] == m2@[1])
{
    m1[0] == m2[0] && m1[1] == m2[1]
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
{
    /* code modified by LLM (iteration 4): Fixed precondition issues and improved loop invariants */
    if magnets.len() == 0 {
        return 0;
    }
    
    let mut groups: usize = 1;
    let mut i: usize = 1;
    
    while i < magnets.len()
        invariant
            1 <= i <= magnets.len(),
            groups >= 1,
            groups <= i,
            valid_input(magnets@.map(|j, v: Vec<char>| v@)),
            forall|k: int| 0 <= k < i ==> magnets@[k]@.len() == 2
        decreases magnets.len() - i
    {
        let current = &magnets[i];
        let previous = &magnets[i-1];
        
        // Assert preconditions for magnets_equal
        assert(valid_input(magnets@.map(|j, v: Vec<char>| v@)));
        assert(0 <= i-1 && i-1 < magnets@.len());
        assert(0 <= i && i < magnets@.len());
        assert(magnets@[i-1]@.len() == 2);
        assert(magnets@[i]@.len() == 2);
        assert(current@.len() == 2);
        assert(previous@.len() == 2);
        
        if !magnets_equal(current, previous) {
            groups = groups + 1;
        }
        i = i + 1;
    }
    
    assert(groups as int == count_groups(magnets@.map(|j, v: Vec<char>| v@)));
    groups
}
// </vc-code>


}

fn main() {}