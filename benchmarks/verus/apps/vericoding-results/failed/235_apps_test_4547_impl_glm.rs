// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn clean_input(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 { 
        s
    } else if s[s.len() - 1] == '\n' || s[s.len() - 1] == '\r' || s[s.len() - 1] == ' ' { 
        clean_input(s.subrange(0, s.len() - 1))
    } else { 
        s
    }
}

spec fn contains_digit_nine(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == '9'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type usage in non-ghost code by using usize for index variable */
fn exec_clean_input(s: &str) -> (result: String)
    ensures result@ == clean_input(s@)
{
    let mut chars: Vec<char> = s.chars().collect();
    let mut i = chars.len();
    while i > 0
        invariant
            0 <= i as int <= chars@.len(),
            clean_input(s@) == clean_input(chars@.subrange(0, i as int))
    {
        let c = chars[i - 1];
        if c == '\n' || c == '\r' || c == ' ' {
            chars.pop();
            i = i - 1;
        } else {
            break;
        }
    }
    proof {
        if i == 0 {
            assert(clean_input(chars@.subrange(0, i as int)) == chars@.subrange(0, i as int));
        } else {
            let last_char = chars@[i - 1];
            assert(last_char != '\n');
            assert(last_char != '\r');
            assert(last_char != ' ');
            assert(clean_input(chars@.subrange(0, i as int)) == chars@.subrange(0, i as int));
        }
    }
    chars.into_iter().collect()
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (result: String)
    requires stdin_input@.len() > 0
    ensures 
        result@ == seq!['Y', 'e', 's', '\n'] || result@ == seq!['N', 'o', '\n'],
        result@ == seq!['Y', 'e', 's', '\n'] <==> contains_digit_nine(clean_input(stdin_input@)),
        result@ == seq!['N', 'o', '\n'] <==> !contains_digit_nine(clean_input(stdin_input@))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): maintained logic with corrected helper function usage */
{
    let cleaned_str = exec_clean_input(stdin_input);
    if cleaned_str.contains('9') {
        "Yes\n".to_string()
    } else {
        "No\n".to_string()
    }
}
// </vc-code>


}

fn main() {}