// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0
}

spec fn valid_parsed_input(parts: Seq<Seq<char>>) -> bool {
    parts.len() == 3 && parts[0].len() > 0 && parts[1].len() > 0 && parts[2].len() > 0
}

spec fn is_word_chain(a: Seq<char>, b: Seq<char>, c: Seq<char>) -> bool {
    a.len() > 0 && b.len() > 0 && c.len() > 0 &&
    a[a.len() - 1] == b[0] && b[b.len() - 1] == c[0]
}

spec fn split_on_spaces(s: Seq<char>) -> Seq<Seq<char>>;

spec fn expected_result(input: Seq<char>) -> Seq<char> {
    let stripped = if input.len() > 0 && input[input.len() - 1] == '\n' {
        input.subrange(0, input.len() - 1)
    } else {
        input
    };
    let parts = split_on_spaces(stripped);
    if valid_parsed_input(parts) {
        if is_word_chain(parts[0], parts[1], parts[2]) {
            seq!['Y', 'E', 'S', '\n']
        } else {
            seq!['N', 'O', '\n']
        }
    } else {
        seq![]
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures result@ == expected_result(input@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed nat/int type mismatches in sequence indexing */
    let mut words: Vec<Vec<char>> = Vec::new();
    let mut current_word: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    // Strip trailing newline if present
    let input_len = input.len();
    let actual_len = if input_len > 0 && input[input_len - 1] == '\n' {
        input_len - 1
    } else {
        input_len
    };
    
    // Parse input into words
    while i < actual_len
        invariant
            0 <= i <= actual_len,
            actual_len <= input.len(),
            words@.len() <= 4,
            current_word@.len() <= actual_len,
        decreases actual_len - i
    {
        if input[i] == ' ' {
            if current_word.len() > 0 && words.len() < 4 {
                words.push(current_word);
                current_word = Vec::new();
            }
        } else {
            if current_word.len() < actual_len {
                current_word.push(input[i]);
            }
        }
        i = i + 1;
    }
    
    // Add last word if non-empty
    if current_word.len() > 0 && words.len() < 4 {
        words.push(current_word);
    }
    
    // Get the stripped sequence for spec comparison
    let stripped = if input@.len() > 0 && input@[input@.len() - 1 as int] == '\n' {
        input@.subrange(0 as int, (input@.len() - 1) as int)
    } else {
        input@
    };
    
    // Check if we have exactly 3 words
    if words.len() != 3 {
        // Assert that when we don't have 3 words, the spec also returns empty
        assert(!valid_parsed_input(split_on_spaces(stripped)));
        return Vec::new();
    }
    
    // Check if all words are non-empty
    if words[0].len() == 0 || words[1].len() == 0 || words[2].len() == 0 {
        // Assert that when words are empty, the spec also returns empty
        assert(!valid_parsed_input(split_on_spaces(stripped)));
        return Vec::new();
    }
    
    // At this point we have valid parsed input
    assert(valid_parsed_input(split_on_spaces(stripped)));
    
    // Check word chain condition
    let word1_last = words[0][words[0].len() - 1];
    let word2_first = words[1][0];
    let word2_last = words[1][words[1].len() - 1];
    let word3_first = words[2][0];
    
    if word1_last == word2_first && word2_last == word3_first {
        let mut result = Vec::new();
        result.push('Y');
        result.push('E');
        result.push('S');
        result.push('\n');
        result
    } else {
        let mut result = Vec::new();
        result.push('N');
        result.push('O');
        result.push('\n');
        result
    }
}
// </vc-code>


}

fn main() {}