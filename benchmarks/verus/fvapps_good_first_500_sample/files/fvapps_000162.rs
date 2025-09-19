// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_subsequence(sub: Seq<char>, word: Seq<char>) -> bool
    decreases word.len()
{
    if sub.len() == 0 {
        true
    } else if word.len() == 0 {
        false
    } else if sub[0] == word[0] {
        is_subsequence(sub.skip(1), word.skip(1))
    } else {
        is_subsequence(sub, word.skip(1))
    }
}

spec fn seq_lex_lt(s1: Seq<char>, s2: Seq<char>) -> bool
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 && s2.len() == 0 {
        false
    } else if s1.len() == 0 {
        true
    } else if s2.len() == 0 {
        false
    } else if s1[0] < s2[0] {
        true
    } else if s1[0] > s2[0] {
        false
    } else {
        seq_lex_lt(s1.skip(1), s2.skip(1))
    }
}
// </vc-helpers>

// <vc-spec>
fn is_subsequence_fn(sub: &str, word: &str) -> (result: bool)
    ensures result == is_subsequence(sub@, word@)
{
    assume(false);
    false
}

fn find_longest_word(s: &str, dict: Vec<String>) -> (result: String)
    ensures
        s@.len() == 0 ==> result@ == Seq::<char>::empty(),
        dict@.len() == 0 ==> result@ == Seq::<char>::empty(),
        result@.len() == 0 || (exists|i: int| 0 <= i < dict@.len() && dict@[i]@ == result@),
        result@.len() == 0 || is_subsequence(result@, s@),
        forall|i: int| 0 <= i < dict@.len() ==> 
            dict@[i]@.len() > result@.len() ==> 
                !is_subsequence(dict@[i]@, s@),
        forall|i: int| 0 <= i < dict@.len() ==> 
            (dict@[i]@.len() == result@.len() && seq_lex_lt(dict@[i]@, result@)) ==> 
                !is_subsequence(dict@[i]@, s@)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>

}

fn main() {
    // let result1 = find_longest_word("abpcplea", vec!["ale".to_string(), "apple".to_string(), "monkey".to_string(), "plea".to_string()]);
    // println!("{}", result1); // Should print "apple"
    
    // let result2 = find_longest_word("abpcplea", vec!["a".to_string(), "b".to_string(), "c".to_string()]);
    // println!("{}", result2); // Should print "a"
    
    // let result3 = find_longest_word("aaa", vec!["aaa".to_string(), "aa".to_string(), "a".to_string()]);
    // println!("{}", result3); // Should print "aaa"
}