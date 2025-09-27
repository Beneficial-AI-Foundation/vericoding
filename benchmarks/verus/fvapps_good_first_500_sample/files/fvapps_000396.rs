// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn chars_differ_by_one(s1: Seq<char>, s2: Seq<char>) -> bool {
    s1.len() == s2.len() && 
    (exists|i: int| 0 <= i < s1.len() && 
     s1[i] != s2[i] && 
     (forall|j: int| 0 <= j < s1.len() && j != i ==> s1[j] == s2[j]))
}

spec fn word_list_contains(word_list: Seq<Seq<char>>, word: Seq<char>) -> bool {
    exists|i: int| 0 <= i < word_list.len() && word_list[i] == word
}

fn ladder_length(begin_word: &str, end_word: &str, word_list: &Vec<String>) -> (result: usize)
    ensures
        result >= 0,
        (!word_list_contains(word_list@.map(|i: int, s: String| s@), end_word@)) ==> result == 0,
        (begin_word@.len() != end_word@.len()) ==> result == 0,
        (word_list_contains(word_list@.map(|i: int, s: String| s@), end_word@) && 
         begin_word@.len() == end_word@.len() && 
         chars_differ_by_one(begin_word@, end_word@)) ==> result == 2
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {
    // let result1 = ladder_length("hit", "cog", &vec!["hot".to_string(), "dot".to_string(), "dog".to_string(), "lot".to_string(), "log".to_string(), "cog".to_string()]);
    // println!("{}", result1); // Should print 5
    
    // let result2 = ladder_length("hit", "cog", &vec!["hot".to_string(), "dot".to_string(), "dog".to_string(), "lot".to_string(), "log".to_string()]);
    // println!("{}", result2); // Should print 0
    
    // let result3 = ladder_length("dog", "cog", &vec!["cog".to_string()]);
    // println!("{}", result3); // Should print 2
}