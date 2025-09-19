// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn letter_count(letters: Seq<char>) -> Map<char, nat>
    decreases letters.len()
{
    if letters.len() == 0 {
        Map::empty()
    } else {
        let head = letters[0];
        let tail_count = letter_count(letters.skip(1));
        if tail_count.dom().contains(head) {
            tail_count.insert(head, tail_count[head] + 1)
        } else {
            tail_count.insert(head, 1)
        }
    }
}

spec fn word_score(word: Seq<char>, scores: Seq<nat>) -> nat
    decreases word.len()
{
    if word.len() == 0 {
        0
    } else {
        let ch = word[0];
        let index = (ch as u8 - 'a' as u8) as nat;
        if index < scores.len() {
            scores[index as int] + word_score(word.skip(1), scores)
        } else {
            0
        }
    }
}

spec fn total_letter_score(letters: Seq<char>, scores: Seq<nat>) -> nat
    decreases letters.len()
{
    if letters.len() == 0 {
        0
    } else {
        let ch = letters[0];
        let index = (ch as u8 - 'a' as u8) as nat;
        if index < scores.len() {
            scores[index as int] + total_letter_score(letters.skip(1), scores)
        } else {
            0
        }
    }
}

fn max_score_words(words: Vec<String>, letters: Vec<char>, scores: Vec<nat>) -> (result: nat)
    requires
        1 <= words.len() <= 14,
        1 <= letters.len() <= 100,
        scores.len() == 26,
        forall|i: int| 0 <= i < scores.len() ==> scores[i] <= 10,
        forall|i: int| 0 <= i < words.len() ==> 1 <= words[i]@.len() <= 15,
        forall|i: int| 0 <= i < letters.len() ==> 'a' <= letters[i] <= 'z',
        forall|i: int| 0 <= i < words.len() ==> forall|j: int| 0 <= j < words[i]@.len() ==> 'a' <= words[i]@[j] <= 'z',
    ensures
        result <= total_letter_score(letters@, scores@),
        result >= 0,
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
    // Example usage (commented out):
    // let words1 = vec!["dog".to_string(), "cat".to_string(), "dad".to_string(), "good".to_string()];
    // let letters1 = vec!['a', 'a', 'c', 'd', 'd', 'd', 'g', 'o', 'o'];
    // let scores1 = vec![1, 0, 9, 5, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    // println!("Result: {}", max_score_words(words1, letters1, scores1));
}