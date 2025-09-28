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
fn find_clean_end(s: &[char]) -> (end_idx: usize)
    ensures
        0 <= end_idx <= s.len(),
        s@.subrange(0, end_idx as int) == clean_input(s@),
{
    let mut i: usize = s.len();
    while i > 0
        invariant
            0 <= i <= s.len(),
            clean_input(s@) == clean_input(s@.subrange(0, i as int)),
        decreases i
    {
        if s[i - 1] == '\n' || s[i - 1] == '\r' || s[i - 1] == ' ' {
            i = i - 1;
        } else {
            break;
        }
    }
    i
}

fn contains_nine(s: &[char]) -> (res: bool)
    ensures res == contains_digit_nine(s@),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            !(exists|j: int| 0 <= j < i as int && s@[j] == '9'),
        decreases s.len() - i
    {
        if s[i] == '9' {
            return true;
        }
        i = i + 1;
    }
    false
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
{
    /* code modified by LLM (iteration 3): use to_vec() and slicing to fix compile error */
    let s_chars = stdin_input.to_vec();
    let end_idx = find_clean_end(&s_chars);
    let clean_slice = &s_chars[..end_idx];
    let has_nine = contains_nine(clean_slice);
    if has_nine {
        "Yes\n".to_string()
    } else {
        "No\n".to_string()
    }
}
// </vc-code>


}

fn main() {}