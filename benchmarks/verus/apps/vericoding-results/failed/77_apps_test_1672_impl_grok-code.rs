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
    /* code modified by LLM (iteration 4): updated invariant to use char comparison, added len assertion in invariant, and revised set definition to match code logic */
    let len = magnets.len();
    if len == 0 {
        return 0;
    }
    let mut groups: usize = 1;
    let mut i: usize = 1;
    while i < len
        invariant
            1 <= i as int <= len as int,
            0 < len as int,
            valid_input(magnets@.map(|i_: int, v: Vec<char>| v@)),
            forall|k: int| 0 <= k < i as int ==> magnets@[k].len() == 2,
            groups as int == 1 + Set::new(|j: int| 1 <= j < i as int && (magnets@[j][0] != magnets@[j-1][0] || magnets@[j][1] != magnets@[j-1][1])).len() as int,
        decreases len as int - i as int,
    {
        if magnets[i][0] != magnets[i - 1][0] || magnets[i][1] != magnets[i - 1][1] {
            groups = groups + 1;
        }
        i = i + 1;
    }
    groups
}
// </vc-code>


}

fn main() {}