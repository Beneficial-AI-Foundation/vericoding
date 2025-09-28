// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate spec function declarations */
spec fn is_alpha_char(c: char) -> bool {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
}

spec fn is_upper_char(c: char) -> bool {
    'A' <= c && c <= 'Z'
}

fn has_alpha_chars_impl(s: &Vec<char>) -> (result: bool)
    ensures result == has_alpha_chars(s@)
{
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> !is_alpha_char(s@[j])
    {
        if is_alpha_char(s[i]) {
            return true;
        }
        i += 1;
    }
    false
}

fn all_alpha_are_upper_impl(s: &Vec<char>) -> (result: bool)
    ensures result == all_alpha_are_upper(s@)
{
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i && is_alpha_char(s@[j]) ==> is_upper_char(s@[j])
    {
        if is_alpha_char(s[i]) && !is_upper_char(s[i]) {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool;

spec fn is_upper_char(c: char) -> bool;

spec fn has_alpha_chars(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_alpha_char(s[i])
}

spec fn all_alpha_are_upper(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() && is_alpha_char(s[i]) ==> is_upper_char(s[i])
}

fn isupper(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i] == {
            let s = a[i]@;
            s.len() > 0 && has_alpha_chars(s) && all_alpha_are_upper(s)
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): unchanged main implementation */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == {
                let s = a[j]@;
                s.len() > 0 && has_alpha_chars(s) && all_alpha_are_upper(s)
            }
    {
        let s_chars: Vec<char> = a[i].chars().collect();
        let has_len = s_chars.len() > 0;
        let has_alpha = if has_len { has_alpha_chars_impl(&s_chars) } else { false };
        let all_upper = if has_len && has_alpha { all_alpha_are_upper_impl(&s_chars) } else { false };
        
        result.push(has_len && has_alpha && all_upper);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}