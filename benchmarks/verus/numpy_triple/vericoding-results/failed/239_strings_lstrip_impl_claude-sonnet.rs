// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatches and using correct sequence indexing */
fn char_should_be_stripped(c: char, chars: Option<String>) -> bool {
    match chars {
        None => c == ' ' || c == '\t' || c == '\n' || c == '\r',
        Some(char_set) => {
            let mut i: usize = 0;
            while i < char_set@.len() as usize
                invariant
                    0 <= i <= char_set@.len(),
            {
                let ch = char_set@[i as int];
                if ch == c {
                    return true;
                }
                i += 1;
            }
            false
        }
    }
}

fn find_first_non_stripped_char(s: &String, chars: Option<String>) -> usize {
    let mut i: usize = 0;
    while i < s@.len() as usize
        invariant
            0 <= i <= s@.len(),
    {
        let ch = s@[i as int];
        if !char_should_be_stripped(ch, chars) {
            return i;
        }
        i += 1;
    }
    s@.len() as usize
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
    /* code modified by LLM (iteration 5): Fixed type mismatches and using correct sequence indexing */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let original = #[trigger] a[j];
                let result_str: String = #[trigger] result[j];
                result_str@.len() <= original@.len() &&
                (exists|k: int| 0 <= k <= original@.len() as int && 
                 result_str@ == original@.subrange(k, original@.len() as int)) &&
                (original@.len() == 0 ==> result_str@.len() == 0)
            },
    {
        let original_str = &a[i];
        let start_pos = find_first_non_stripped_char(original_str, chars);
        
        let stripped_str = if start_pos >= original_str@.len() as usize {
            String::new()
        } else {
            let mut new_str = String::new();
            let mut j: usize = start_pos;
            while j < original_str@.len() as usize
                invariant
                    start_pos <= j <= original_str@.len(),
            {
                let ch = original_str@[j as int];
                new_str.push(ch);
                j += 1;
            }
            new_str
        };
        
        result.push(stripped_str);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}