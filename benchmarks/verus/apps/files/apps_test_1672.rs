// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(magnets: Seq<Seq<char>>) -> bool {
    forall|i: int| 0 <= i < magnets.len() ==> (
        magnets[i].len() == 2 &&
        ((magnets[i][0] == '0' && magnets[i][1] == '1') ||
         (magnets[i][0] == '1' && magnets[i][1] == '0'))
    )
}

spec fn count_groups(magnets: Seq<Seq<char>>) -> int
    recommends valid_input(magnets)
{
    if magnets.len() == 0 { 
        0
    } else {
        1 + Set::new(|i: int| 1 <= i < magnets.len() && magnets[i] != magnets[i-1]).len()
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(magnets: Seq<Seq<char>>) -> (result: int)
    requires
        valid_input(magnets)
    ensures
        result >= 0,
        magnets.len() == 0 ==> result == 0,
        magnets.len() > 0 ==> result >= 1,
        result <= magnets.len(),
        result == count_groups(magnets)
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}