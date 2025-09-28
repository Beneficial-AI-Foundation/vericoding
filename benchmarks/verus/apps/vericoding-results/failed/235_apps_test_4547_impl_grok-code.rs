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
    /* code modified by LLM (iteration 5): Fixed character literals by escaping newlines and carriage returns */
    let chars_vec: Vec<char> =
        stdin_input.chars().collect();
    let mut cleaned_len: usize = chars_vec.len();
    while cleaned_len > 0 {
        let end_idx = cleaned_len - 1;
        if chars_vec[end_idx] == '\n' || chars_vec[end_idx] == '\r' || chars_vec[end_idx] == ' ' {
            cleaned_len -= 1;
        } else {
            break;
        }
    }
    let spec_chars = stdin_input@;
    proof {
        let spec_cleaned = clean_input(spec_chars);
        assert(spec_cleaned.len() == cleaned_len as nat);
        assert(forall|i: nat| #![trigger spec_cleaned[i]] i < cleaned_len as nat ==>
            (spec_cleaned[i] == chars_vec@[i as int]));
    }
    let has_nine: bool = (0..cleaned_len).any(|i| chars_vec[i] == '9');
    proof {
        let cleaned_seq = spec_chars;
        assert(contains_digit_nine(clean_input(cleaned_seq)) == has_nine);
    }
    if has_nine {
        "Yes\n".to_string()
    } else {
        "No\n".to_string()
    }
}
// </vc-code>


}

fn main() {}