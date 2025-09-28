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
fn is_in_group1(c: char) -> (res: bool)
    requires
        'A' <= c <= 'Z',
    ensures
        res <==> group1().contains(c),
{
    reveal(group1);
    c == 'A' || c == 'E' || c == 'F' || c == 'H' || c == 'I' || c == 'K' || c == 'L' || 
    c == 'M' || c == 'N' || c == 'T' || c == 'V' || c == 'W' || c == 'X' || c == 'Y' || c == 'Z'
}

fn is_in_group2(c: char) -> (res: bool)
    requires
        'A' <= c <= 'Z',
    ensures
        res <==> group2().contains(c),
{
    reveal(group2);
    c == 'B' || c == 'C' || c == 'D' || c == 'G' || c == 'J' || c == 'O' || 
    c == 'P' || c == 'Q' || c == 'R' || c == 'S' || c == 'U'
}
// </vc-helpers>

// <vc-spec>
fn solve(word: Vec<char>) -> (result: Vec<char>)
    requires valid_input(word@)
    ensures (all_in_same_group(word@) <==> result@ == seq!['Y','E','S']) && (result@ == seq!['Y','E','S'] || result@ == seq!['N','O'])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added valid_input to loop invariant to prove char range */
    let mut all_g1 = true;
    let mut all_g2 = true;
    let mut i: usize = 0;

    while i < word.len()
        invariant
            valid_input(word@),
            0 <= i <= word.len(),
            all_g1 <==> (forall|k: int| 0 <= k < i ==> group1().contains(word@[k])),
            all_g2 <==> (forall|k: int| 0 <= k < i ==> group2().contains(word@[k])),
        decreases word.len() - i
    {
        let c = word[i];

        if !is_in_group1(c) {
            all_g1 = false;
        }

        if !is_in_group2(c) {
            all_g2 = false;
        }

        i = i + 1;
    }

    proof {
        reveal(all_in_group1);
        reveal(all_in_group2);
        reveal(all_in_same_group);
    }

    if all_g1 || all_g2 {
        vec!['Y', 'E', 'S']
    } else {
        vec!['N', 'O']
    }
}
// </vc-code>


}

fn main() {}