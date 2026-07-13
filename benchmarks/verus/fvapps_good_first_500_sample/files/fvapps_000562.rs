// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn all_chars_known(word: Seq<char>, known_letters: Seq<char>) -> bool {
    forall|c: char| word.contains(c) ==> known_letters.contains(c)
}

spec fn some_char_unknown(word: Seq<char>, known_letters: Seq<char>) -> bool {
    exists|c: char| word.contains(c) && !known_letters.contains(c)
}

fn can_read_words(known_letters: &str, word_list: &Vec<String>) -> (result: Vec<String>)
    requires known_letters@.len() > 0,
    ensures 
        result@.len() == word_list@.len(),
        forall|i: int| 0 <= i < result@.len() ==> (result@[i]@ == "Yes"@ || result@[i]@ == "No"@),
        forall|i: int| 0 <= i < result@.len() && result@[i]@ == "Yes"@ ==> 
            all_chars_known(word_list@[i]@, known_letters@),
        forall|i: int| 0 <= i < result@.len() && result@[i]@ == "No"@ ==> 
            some_char_unknown(word_list@[i]@, known_letters@),
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
    // let result1 = can_read_words("act", &vec!["cat".to_string(), "dog".to_string()]);
    // println!("{:?}", result1); // Should output: ["Yes", "No"]
    
    // let result2 = can_read_words("a", &vec!["a".to_string(), "b".to_string(), "aa".to_string()]);
    // println!("{:?}", result2); // Should output: ["Yes", "No", "Yes"]
    
    // let result3 = can_read_words("xyz", &vec!["x".to_string(), "xy".to_string(), "xyz".to_string(), "abc".to_string()]);
    // println!("{:?}", result3); // Should output: ["Yes", "Yes", "Yes", "No"]
}