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
/* helper modified by LLM (iteration 2): added decreases clauses to while loops */
exec fn is_in_group1(c: char) -> (result: bool)
    ensures result == group1().contains(c)
{
    match c {
        'A' | 'E' | 'F' | 'H' | 'I' | 'K' | 'L' | 'M' | 'N' | 'T' | 'V' | 'W' | 'X' | 'Y' | 'Z' => true,
        _ => false,
    }
}

exec fn is_in_group2(c: char) -> (result: bool)
    ensures result == group2().contains(c)
{
    match c {
        'B' | 'C' | 'D' | 'G' | 'J' | 'O' | 'P' | 'Q' | 'R' | 'S' | 'U' => true,
        _ => false,
    }
}

exec fn check_all_in_group1(word: &Vec<char>) -> (result: bool)
    requires valid_input(word@)
    ensures result == all_in_group1(word@)
{
    let mut i = 0;
    while i < word.len()
        invariant
            0 <= i <= word.len(),
            forall|j: int| 0 <= j < i ==> group1().contains(word@[j])
        decreases word.len() - i
    {
        if !is_in_group1(word[i]) {
            return false;
        }
        i += 1;
    }
    true
}

exec fn check_all_in_group2(word: &Vec<char>) -> (result: bool)
    requires valid_input(word@)
    ensures result == all_in_group2(word@)
{
    let mut i = 0;
    while i < word.len()
        invariant
            0 <= i <= word.len(),
            forall|j: int| 0 <= j < i ==> group2().contains(word@[j])
        decreases word.len() - i
    {
        if !is_in_group2(word[i]) {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn solve(word: Vec<char>) -> (result: Vec<char>)
    requires valid_input(word@)
    ensures (all_in_same_group(word@) <==> result@ == seq!['Y','E','S']) && (result@ == seq!['Y','E','S'] || result@ == seq!['N','O'])
// </vc-spec>
// <vc-code>
{
    if check_all_in_group1(&word) || check_all_in_group2(&word) {
        vec!['Y', 'E', 'S']
    } else {
        vec!['N', 'O']
    }
}
// </vc-code>


}

fn main() {}