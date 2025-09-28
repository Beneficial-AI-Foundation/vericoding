// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helper for character checking */
spec fn is_word_separator(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n'
}

/* helper modified by LLM (iteration 5): convert str to Vec<char> using vstd */
fn str_to_chars(s: &str) -> Vec<char> {
    let mut chars = Vec::new();
    let mut iter = s.chars();
    while let Some(c) = iter.next() {
        chars.push(c);
    }
    chars
}

/* helper modified by LLM (iteration 5): convert Vec<char> to String using vstd */
fn chars_to_string(chars: Vec<char>) -> String {
    let mut result = String::new();
    for i in 0..chars.len() {
        result.push(chars[i]);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn reverse_words(words_str: &str) -> (result: String)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using manual char iteration instead of collect() */
    let chars = str_to_chars(words_str);
    let mut words: Vec<Vec<char>> = Vec::new();
    let mut current_word: Vec<char> = Vec::new();
    let mut in_word = false;
    
    for i in 0..chars.len()
        invariant
            words.len() <= chars.len(),
            current_word.len() <= chars.len()
    {
        let c = chars[i];
        if c == ' ' || c == '\t' || c == '\n' {
            if in_word {
                words.push(current_word.clone());
                current_word = Vec::new();
                in_word = false;
            }
        } else {
            current_word.push(c);
            in_word = true;
        }
    }
    
    if in_word {
        words.push(current_word);
    }
    
    let mut result_chars: Vec<char> = Vec::new();
    
    for i in 0..words.len()
        invariant
            result_chars.len() <= chars.len() * 2
    {
        let word_idx = words.len() - 1 - i;
        for j in 0..words[word_idx].len()
            invariant
                result_chars.len() <= chars.len() * 2
        {
            result_chars.push(words[word_idx][j]);
        }
        if i < words.len() - 1 {
            result_chars.push(' ');
        }
    }
    
    chars_to_string(result_chars)
}
// </vc-code>

}
fn main() {}