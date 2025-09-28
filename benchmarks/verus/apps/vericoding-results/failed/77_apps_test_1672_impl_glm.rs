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
/* code modified by LLM (iteration 5): fixed trigger issue in quantifier */
{
    let n = magnets.len();
    if n == 0 {
        return 0;
    }
    let mut count: usize = 1;
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i <= n,
            (count as int) == 1 + (Set::new(|j: int| 1 <= j < i && magnets@[j] != magnets@[j-1]).len()),
            forall|j: int| 1 <= j < i ==> 
                (#[trigger] magnets@[j] != magnets@[j-1]) ==> (magnets[j][0] != magnets[j-1][0] || magnets[j][1] != magnets[j-1][1]),
            forall|j: int| 1 <= j < i ==> 
                (magnets[j][0] != magnets[j-1][0] || magnets[j][1] != magnets[j-1][1]) ==> (#[trigger] magnets@[j] != magnets@[j-1]),
        decreases n - i
    {
        let cond = magnets[i][0] != magnets[i-1][0] || magnets[i][1] != magnets[i-1][1];
        if cond {
            count += 1;
        }
        proof {
            if cond {
                assert(magnets@[i as int] != magnets@[(i-1) as int]);
            } else {
                assert(magnets@[i as int] == magnets@[(i-1) as int]);
            }
        }
        i += 1;
    }
    count
}
// </vc-code>


}

fn main() {}