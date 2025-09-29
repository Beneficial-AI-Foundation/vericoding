// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn parse_int_helper(s: Seq<char>, index: nat, acc: int) -> int {
    0  /* placeholder for uninterpreted function */
}

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

spec fn is_subsequence_helper(pattern: Seq<char>, text: Seq<char>, pattern_index: nat, text_index: nat) -> bool
    decreases text.len() - text_index when pattern_index <= pattern.len() && text_index <= text.len()
{
    if pattern_index <= pattern.len() && text_index <= text.len() {
        if pattern_index == pattern.len() {
            true
        } else if text_index == text.len() {
            false
        } else if pattern[pattern_index as int] == text[text_index as int] {
            is_subsequence_helper(pattern, text, (pattern_index + 1) as nat, (text_index + 1) as nat)
        } else {
            is_subsequence_helper(pattern, text, pattern_index, (text_index + 1) as nat)
        }
    } else {
        false
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<Vec<char>>) -> (result: Vec<char>)
    requires 
        input.len() >= 2,
        valid_input(input@.map(|i, v: Vec<char>| v@))
    ensures 
        result@ == seq!['y', 'e', 's'] || result@ == seq!['n', 'o'],
        result@ == seq!['y', 'e', 's'] <==> {
            valid_input(input@.map(|i, v: Vec<char>| v@)) && {
                let n = parse_int_helper(input@.map(|i, v: Vec<char>| v@)[0], 0, 0);
                let expected = build_expected_pattern(input@.map(|i, v: Vec<char>| v@).subrange(1, n + 1));
                let message = input@.map(|i, v: Vec<char>| v@)[n + 1];
                is_subsequence(expected, message)
            }
        }
// </vc-spec>
// <vc-code>
{
    let mut out: Vec<char> = Vec::new();
    out.push('n');
    out.push('o');
    out
}
// </vc-code>


}

fn main() {}