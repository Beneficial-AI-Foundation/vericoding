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
/* helper modified by LLM (iteration 2): Added decreases clause to while loop */
proof fn lemma_group_classification(c: char)
    ensures
        ('A' <= c <= 'Z') ==> (group1().contains(c) || group2().contains(c)),
        ('A' <= c <= 'Z') ==> !(group1().contains(c) && group2().contains(c))
{
    // The proof is by the definition of group1() and group2()
}

fn is_in_group1(c: char) -> (result: bool)
    requires 'A' <= c <= 'Z'
    ensures result == group1().contains(c)
{
    let group1_chars = vec!['A','E','F','H','I','K','L','M','N','T','V','W','X','Y','Z'];
    let mut i = 0;
    while i < group1_chars.len()
        invariant
            0 <= i <= group1_chars.len(),
            group1_chars@ == group1(),
            forall|j: int| 0 <= j < i ==> group1_chars@[j] != c,
        decreases group1_chars.len() - i
    {
        if group1_chars[i] == c {
            assert(group1_chars@[i as int] == c);
            assert(group1().contains(c));
            return true;
        }
        i = i + 1;
    }
    assert(forall|j: int| 0 <= j < group1_chars.len() ==> group1_chars@[j] != c);
    assert(!group1().contains(c));
    false
}

fn check_all_in_same_group(word: &Vec<char>) -> (result: bool)
    requires valid_input(word@)
    ensures result == all_in_same_group(word@)
{
    if word.len() == 0 {
        return true;
    }
    
    let first_in_group1 = is_in_group1(word[0]);
    proof {
        lemma_group_classification(word[0]);
    }
    
    let mut i = 1;
    while i < word.len()
        invariant
            1 <= i <= word.len(),
            valid_input(word@),
            first_in_group1 == group1().contains(word@[0]),
            forall|j: int| 0 <= j < i ==> (
                if first_in_group1 {
                    group1().contains(word@[j])
                } else {
                    group2().contains(word@[j])
                }
            ),
        decreases word.len() - i
    {
        let c_in_group1 = is_in_group1(word[i]);
        proof {
            lemma_group_classification(word[i as int]);
        }
        
        if c_in_group1 != first_in_group1 {
            assert(!all_in_same_group(word@));
            return false;
        }
        i = i + 1;
    }
    
    if first_in_group1 {
        assert(all_in_group1(word@));
    } else {
        assert(all_in_group2(word@));
    }
    assert(all_in_same_group(word@));
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
    /* code modified by LLM (iteration 2): No changes needed, code is correct */
    let same_group = check_all_in_same_group(&word);
    
    if same_group {
        vec!['Y', 'E', 'S']
    } else {
        vec!['N', 'O']
    }
}
// </vc-code>


}

fn main() {}