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
/* helper modified by LLM (iteration 5): Removed unnecessary helper from the previous implementation that was not being used. */
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
/* code modified by LLM (iteration 5): Corrected indexing for `magnets` inside the loop by mapping `Vec<char>` to `Seq<char>` before using `@` indexer. Additionally, fixed the type mismatch for `take` method by casting `i` to `int`. */
{
    let n = magnets.len();
    if n == 0 {
        return 0;
    }

    let mut groups: usize = 0;
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i && i <= n,
            groups == count_groups(magnets@.map(|k, v: Vec<char>| v@).take(i as int)) as usize,
            valid_input(magnets@.map(|k, v: Vec<char>| v@))
        decreases (n - i)
    {
        if i == 0 {
            groups = 1;
        } else {
            let magnets_seq = magnets@.map(|k, v: Vec<char>| v@);
            if magnets_seq@[i as int] != magnets_seq@[(i - 1) as int] {
                groups = groups + 1;
            }
        }
        i = i + 1;
    }
    
    groups
}
// </vc-code>


}

fn main() {}