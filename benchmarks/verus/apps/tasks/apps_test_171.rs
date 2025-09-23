// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn contains_lowercase(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && 'a' <= s[i] && s[i] <= 'z'
}

spec fn contains_uppercase(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && 'A' <= s[i] && s[i] <= 'Z'
}

spec fn contains_digit(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && '0' <= s[i] && s[i] <= '9'
}

spec fn is_valid_password(s: Seq<char>) -> bool {
    s.len() >= 5 && contains_lowercase(s) && contains_uppercase(s) && contains_digit(s)
}

spec fn trim_newline(s: Seq<char>) -> Seq<char> {
    if s.len() > 0 && s[s.len() as int - 1] == '\n' { 
        s.subrange(0, s.len() as int - 1) 
    } else { 
        s 
    }
}

spec fn strip_whitespace(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 { 
        s
    } else if s[0] == ' ' || s[0] == '\t' || s[0] == '\n' || s[0] == '\r' {
        strip_whitespace(s.subrange(1, s.len() as int))
    } else if s[s.len() as int - 1] == ' ' || s[s.len() as int - 1] == '\t' || s[s.len() as int - 1] == '\n' || s[s.len() as int - 1] == '\r' {
        strip_whitespace(s.subrange(0, s.len() as int - 1))
    } else { 
        s 
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (output: Vec<char>)
    requires input@.len() > 0
    ensures ({
        let processed_input = trim_newline(input@);
        let stripped = strip_whitespace(processed_input);
        if is_valid_password(stripped) {
            output@ == seq!['C', 'o', 'r', 'r', 'e', 'c', 't', '\n']
        } else {
            output@ == seq!['T', 'o', 'o', ' ', 'w', 'e', 'a', 'k', '\n']
        }
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}