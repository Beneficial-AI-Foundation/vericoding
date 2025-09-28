// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn reverse_words(words_str: &str) -> (result: String)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): replaced unsupported char_indices() with while loop and chars() */
    let mut tokens: Vec<(&str, bool)> = Vec::new();
    let mut start = 0;
    let mut is_word = false;

    let mut chars_iter = words_str.chars();
    let mut i = 0; // current byte index

    while let Some(c) = chars_iter.next() {
        let char_len = c.len_utf8();

        if c == ' ' {
            if is_word {
                // End of a word: push the word from `start` to `i`
                tokens.push((&words_str[start..i], true));
                start = i; // the space starts at the current byte index
                is_word = false;
            }
            // Otherwise, we are already in a space, do nothing
        } else {
            if !is_word {
                // End of a space: push the space from `start` to `i` (if non-empty)
                if start < i {
                    tokens.push((&words_str[start..i], false));
                }
                start = i; // the word starts at the current byte index
                is_word = true;
            }
            // Otherwise, we are already in a word, do nothing
        }

        i += char_len;
    }

    // Push the last token
    if start < words_str.len() {
        tokens.push((&words_str[start..], is_word));
    }

    // Extract words and reverse
    let mut words: Vec<&str> = tokens.iter().filter(|(_, is_word)| *is_word).map(|(s, _)| *s).collect();
    words.reverse();

    // Reassemble the string
    let mut result = String::new();
    let mut word_iter = words.into_iter();
    for (token, is_word) in tokens {
        if is_word {
            result.push_str(word_iter.next().unwrap());
        } else {
            result.push_str(token);
        }
    }
    result
}
// </vc-code>

}
fn main() {}