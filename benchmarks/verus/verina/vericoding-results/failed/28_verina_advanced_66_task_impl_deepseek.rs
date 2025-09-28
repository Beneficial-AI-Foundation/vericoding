// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_split_at_char(s: Seq<char>, c: char, i: int) -> (Seq<char>, Seq<char>)
    requires
        0 <= i < s.len(),
        s[i] === c,
    ensures
        let (s1, s2) = (result.0, result.1);
        s1 === s.subrange(0, i),
        s2 === s.subrange(i + 1, s.len()),
        s === s1.insert(i, c) + s2,
{
    let s1 = s.subrange(0, i);
    let s2 = s.subrange(i + 1, s.len());
    proof {
        assert(s === s.subrange(0, i) + s.subrange(i, s.len()));
        assert(s.subrange(i, s.len()) === seq![s[i]] + s2);
    }
    (s1, s2)
}

proof fn lemma_reverse_words_recursive(s: Seq<char>, result: Seq<char>, acc: int) -> Seq<char>
    requires
        acc >= 0,
        result.len() == acc - s.len(),
    ensures
        result.len() == acc,
{
    if s.is_empty() {
        result
    } else {
        let idx = s.index_of(|ch| ch === ' ');
        if idx.is_some() {
            let i = idx.get_Some_0();
            let s1 = s.subrange(0, i);
            let s2 = s.subrange(i + 1, s.len());
            let reversed_word = s1.reverse();
            let new_result = reversed_word + seq![' '] + result;
            lemma_reverse_words_recursive(s2, new_result, acc)
        } else {
            let reversed_word = s.reverse();
            reversed_word + result
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn reverse_words(words_str: &str) -> (result: String)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed return type syntax in lemma_split_at_char and recursive helper */
    let mut result = String::new();
    let mut words: Vec<&str> = words_str.split(' ').collect();
    words.reverse();
    
    for word in words.iter() {
        result.push_str(word);
        result.push(' ');
    }
    
    if !result.is_empty() {
        result.pop();
    }
    
    result
}
// </vc-code>

}
fn main() {}