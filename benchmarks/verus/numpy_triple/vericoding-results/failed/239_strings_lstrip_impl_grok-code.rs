// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): define spec functions for strip logic */
pub open spec fn is_whitespace(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

pub open spec fn is_strip_char(c: char, chars_option: Option<String>) -> bool {
    match chars_option {
        Option::Some(ch_str) => ch_str@.contains(c),
        Option::None => is_whitespace(c),
    }
}

pub open spec fn find_start(s: Seq<char>, chars_option: Option<String>) -> (result: int)
    decreases s.len()
    ensures
        0 <= result <= s.len(),
        forall|i: int| 0 <= i < result ==> is_strip_char(s[i], chars_option),
        (result < s.len() ==> !is_strip_char(s[result], chars_option)) || (result == s.len())
{
    if s.len() == 0 {
        0
    } else if is_strip_char(s[0], chars_option) {
        1 + find_start(s.drop_first(), chars_option)
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn lstrip(a: Vec<String>, chars: Option<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() as int ==> {
            let original = #[trigger] a[i];
            let result_str = #[trigger] result[i];

            result_str@.len() <= original@.len() &&

            (exists|k: int| 0 <= k <= original@.len() as int && 
             result_str@ == original@.subrange(k, original@.len() as int)) &&

            (original@.len() == 0 ==> result_str@.len() == 0)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement lstrip using spec functions to find strip position with verification */
    let mut result: Vec<String> = Vec::new();
    for i in 0..a.len()
    {
        let s = &a[i];
        let mut pos = 0;
        while pos < s@.len()
            invariant
                0 <= pos <= s@.len(),
                forall|j| 0 <= j < pos ==> is_strip_char(s@[j], chars)
        {
            let c = s.chars().nth(pos);
            let c_val = match c {
                None => char::REPLACEMENT_CHARACTER, // though not reached
                Some(ch) => ch
            };
            if !is_strip_char(c_val, chars) {
                break;
            }
            pos += 1;
        }
        let start = pos;
        let new_s: String = if start >= s@.len() {
            String::new()
        } else {
            s.chars().skip(start).collect()
        };
        result.push(new_s);
    }
    result
}
// </vc-code>

}
fn main() {}