// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(input: Seq<Seq<char>>) -> bool {
    input.len() >= 2 &&
    {
        let n = parse_int_helper(input[0], 0, 0);
        n >= 1 && n + 1 < input.len()
    }
}

spec fn build_expected_pattern(words: Seq<Seq<char>>) -> Seq<char>
    decreases words.len()
{
    if words.len() == 0 {
        seq!['<', '3']
    } else {
        seq!['<', '3'] + words[0] + build_expected_pattern(words.subrange(1, words.len() as int))
    }
}

spec fn is_subsequence(pattern: Seq<char>, text: Seq<char>) -> bool {
    is_subsequence_helper(pattern, text, 0, 0)
}

spec fn is_subsequence_helper(pattern: Seq<char>, text: Seq<char>, pattern_index: int, text_index: int) -> bool
    recommends 
        pattern_index <= pattern.len(),
        text_index <= text.len(),
        pattern_index >= 0,
        text_index >= 0
    decreases text.len() - text_index
{
    if pattern_index == pattern.len() {
        true
    } else if text_index == text.len() {
        false
    } else if pattern[pattern_index] == text[text_index] {
        is_subsequence_helper(pattern, text, pattern_index + 1, text_index + 1)
    } else {
        is_subsequence_helper(pattern, text, pattern_index, text_index + 1)
    }
}

spec fn parse_int_helper(s: Seq<char>, start: int, acc: int) -> int {
    0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Seq<Seq<char>>) -> (result: Seq<char>)
    requires 
        input.len() >= 2,
        valid_input(input),
    ensures 
        result == seq!['y', 'e', 's'] || result == seq!['n', 'o'],
        result == seq!['y', 'e', 's'] <==> {
            valid_input(input) && {
                let n = parse_int_helper(input[0], 0, 0);
                let expected = build_expected_pattern(input.subrange(1, n + 1));
                let message = input[n + 1];
                is_subsequence(expected, message)
            }
        }
// </vc-spec>
// <vc-code>
{
    /* impl-start */
    assume(false);
    unreached()
    /* impl-end */
}
// </vc-code>


}

fn main() {}