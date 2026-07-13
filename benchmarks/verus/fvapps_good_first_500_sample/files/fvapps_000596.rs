// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_bubbly_spec(word: Seq<char>) -> bool {
    true  /* placeholder specification */
}

fn is_bubbly(word: Vec<char>) -> (result: bool)
    ensures result == is_bubbly_spec(word@)
{
    // impl-start
    assume(false);
    false
    // impl-end
}

spec fn count_bubbly_words_spec(words: Seq<Vec<char>>) -> nat
    decreases words.len()
{
    if words.len() == 0 {
        0nat
    } else {
        (if is_bubbly_spec(words[0]@) { 1nat } else { 0nat }) + count_bubbly_words_spec(words.skip(1))
    }
}

fn count_bubbly_words(words: Vec<Vec<char>>) -> (result: usize)
    ensures 
        result as nat == count_bubbly_words_spec(words@),
        result <= words.len()
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
    // let test_words = vec![
    //     vec!['A', 'B', 'A', 'B'],
    //     vec!['A', 'A', 'B', 'B'], 
    //     vec!['A', 'B', 'B', 'A']
    // ];
    // let result = count_bubbly_words(test_words);
    // println!("{}", result);
}