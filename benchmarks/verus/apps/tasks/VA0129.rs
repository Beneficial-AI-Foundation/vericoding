// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(word: Seq<char>) -> bool {
    1 <= word.len() <= 10 && forall|i: int| 0 <= i < word.len() ==> 'A' <= #[trigger] word[i] <= 'Z'
}

spec fn group1() -> Seq<char> { 
    seq!['A','E','F','H','I','K','L','M','N','T','V','W','X','Y','Z']
}

spec fn group2() -> Seq<char> { 
    seq!['B','C','D','G','J','O','P','Q','R','S','U']
}

spec fn all_in_group1(word: Seq<char>) -> bool {
    forall|i: int| 0 <= i < word.len() ==> group1().contains(#[trigger] word[i])
}

spec fn all_in_group2(word: Seq<char>) -> bool {
    forall|i: int| 0 <= i < word.len() ==> group2().contains(#[trigger] word[i])
}

spec fn all_in_same_group(word: Seq<char>) -> bool {
    all_in_group1(word) || all_in_group2(word)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(word: Vec<char>) -> (result: Vec<char>)
    requires valid_input(word@)
    ensures (all_in_same_group(word@) <==> result@ == seq!['Y','E','S']) && (result@ == seq!['Y','E','S'] || result@ == seq!['N','O'])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}