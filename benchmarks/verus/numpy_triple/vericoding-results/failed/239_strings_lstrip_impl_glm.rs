// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn lstrip_single(s: String, chars: Option<String>) -> (result: String)
    ensures
        result@.len() <= s@.len(),
        (exists|k: int| 0 <= k <= s@.len() as int && 
         result@ == s@.subrange(k, s@.len() as int)),
        (s@.len() == 0 ==> result@.len() == 0)
{
    /* helper modified by LLM (iteration 5): fixed usize indexing issue in exec code */
    let chars_to_remove = if chars.is_some() {
        chars.unwrap()
    } else {
        " \t\r\n".to_string()
    };

    let char_set: std::collections::HashSet<char> = chars_to_remove.chars().collect();

    if s.is_empty() {
        s
    } else {
        let s_chars: Vec<char> = s.chars().collect();
        let s_len = s_chars.len();

        let mut i: usize = 0;
        while i < s_len && char_set.contains(&s_chars[i]) {
            i += 1;
        }

        let result_chars = &s_chars[i..];
        let result: String = result_chars.iter().collect();

        proof {
            assert(s@.len() == s_chars.len() as int);
            assert(result@.len() == (s_chars.len() - i) as int);
            assert(result@.len() <= s@.len());
            assert(result@ == s@.subrange(i as int, s@.len() as int));
        }

        result
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
/* code modified by LLM (iteration 5): fixed type annotation in invariant */
{
    let mut result = Vec::new();
    let mut i = 0;
    let a_len = a.len();
    
    while i < a_len
        invariant
            0 <= i <= a_len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let original = #[trigger] a[j];
                let result_str: String = #[trigger] result[j];
                
                result_str@.len() <= original@.len() &&
                (exists|k: int| 0 <= k <= original@.len() as int && 
                 result_str@ == original@.subrange(k, original@.len() as int)) &&
                (original@.len() == 0 ==> result_str@.len() == 0)
            }
        decreases a_len - i
    {
        let stripped = lstrip_single(a[i], chars.clone());
        result.push(stripped);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}