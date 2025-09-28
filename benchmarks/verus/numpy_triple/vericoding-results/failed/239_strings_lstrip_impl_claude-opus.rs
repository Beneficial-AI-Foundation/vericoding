// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_whitespace(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

spec fn should_strip(c: char, chars: &Option<String>) -> bool {
    match chars {
        Some(s) => s@.contains(c),
        None => is_whitespace(c),
    }
}

fn is_whitespace_impl(c: char) -> (result: bool)
    ensures result == is_whitespace(c)
{
    c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

fn should_strip_impl(c: char, chars: &Option<String>) -> (result: bool)
    ensures result == should_strip(c, chars)
{
    /* helper modified by LLM (iteration 5): Using unicode_len() for String length */
    match chars {
        Some(s) => {
            let mut i: usize = 0;
            let mut found = false;
            while i < s.unicode_len()
                invariant
                    0 <= i <= s.unicode_len(),
                    found == s@.subrange(0, i as int).contains(c),
            {
                if s.get_char(i) == c {
                    found = true;
                    break;
                }
                i = i + 1;
            }
            found
        },
        None => is_whitespace_impl(c),
    }
}

fn lstrip_single(s: &String, chars: &Option<String>) -> (result: String)
    ensures
        result@.len() <= s@.len(),
        exists|k: int| 0 <= k <= s@.len() as int && 
            result@ == s@.subrange(k, s@.len() as int),
        s@.len() == 0 ==> result@.len() == 0,
{
    let mut i: usize = 0;
    let s_view = s@;
    
    while i < s.unicode_len()
        invariant
            0 <= i <= s.unicode_len(),
            forall|j: int| 0 <= j < i ==> should_strip(s_view[j], chars),
    {
        let c = s.get_char(i);
        if !should_strip_impl(c, chars) {
            break;
        }
        i = i + 1;
    }
    
    s.substring_char(i, s.unicode_len()).to_string()
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
    /* code modified by LLM (iteration 5): Building result vector with proper iteration */
    let mut result = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> {
                let original = #[trigger] a[i];
                let result_str: String = #[trigger] result[i];
                result_str@.len() <= original@.len() &&
                (exists|k: int| 0 <= k <= original@.len() as int && 
                 result_str@ == original@.subrange(k, original@.len() as int)) &&
                (original@.len() == 0 ==> result_str@.len() == 0)
            },
    {
        let stripped = lstrip_single(&a[idx], &chars);
        result.push(stripped);
        idx = idx + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}