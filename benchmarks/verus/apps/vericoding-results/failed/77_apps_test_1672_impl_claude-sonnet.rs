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
/* helper modified by LLM (iteration 5): updated to use proper Verus map syntax and sequence equality */
proof fn groups_properties(magnets: Seq<Seq<char>>)
    requires
        valid_input(magnets)
    ensures
        count_groups(magnets) >= 0,
        magnets.len() == 0 ==> count_groups(magnets) == 0,
        magnets.len() > 0 ==> count_groups(magnets) >= 1,
        count_groups(magnets) <= magnets.len()
{
    if magnets.len() == 0 {
        return;
    }
    
    let groups = count_groups(magnets);
    let changes = Set::new(|i: int| 1 <= i < magnets.len() && magnets[i] != magnets[i-1]).len() as int;
    
    assert(groups == 1 + changes);
    assert(changes >= 0);
    assert(changes <= magnets.len() - 1);
}

proof fn group_count_correctness(magnets: Seq<Seq<char>>, i: int)
    requires
        valid_input(magnets),
        0 <= i < magnets.len()
    ensures
        i == 0 || magnets[i] == magnets[i-1] || magnets[i] != magnets[i-1]
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
{
    /* code modified by LLM (iteration 5): fixed map usage and sequence comparison */
    if magnets.len() == 0 {
        return 0;
    }
    
    let magnet_seq = magnets@.map_values(|v: Vec<char>| v@);
    
    proof {
        groups_properties(magnet_seq);
    }
    
    let mut groups: usize = 1;
    let mut i: usize = 1;
    
    while i < magnets.len()
        invariant
            1 <= i <= magnets.len(),
            groups >= 1,
            groups <= i,
            valid_input(magnet_seq),
            groups == (1 + Set::new(|j: int| 1 <= j < i && magnet_seq[j] != magnet_seq[j-1]).len()) as usize
        decreases magnets.len() - i
    {
        if !magnets[i]@.ext_equal(magnets[i-1]@) {
            groups = groups + 1;
        }
        
        proof {
            group_count_correctness(magnet_seq, i as int);
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == magnets.len());
        assert(groups == count_groups(magnet_seq) as usize);
    }
    
    groups
}
// </vc-code>


}

fn main() {}