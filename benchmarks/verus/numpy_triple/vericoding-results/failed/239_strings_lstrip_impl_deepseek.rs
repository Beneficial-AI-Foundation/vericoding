// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed sequence containment syntax and proof helper */
fn strip_start(s: String, chars: String) -> (stripped: String)
    ensures
        stripped@.len() <= s@.len(),
        exists|k: int| 0 <= k <= s@.len() && stripped@ == s@.subrange(k, s@.len()),
        s@.len() == 0 ==> stripped@.len() == 0
{
    let mut start = 0 as usize;
    let s_len = s.len();
    let chars_set = chars;
    
    while start < s_len
        invariant
            0 <= start <= s_len,
            forall|j: int| 0 <= j < start ==> chars_set@.contains(s@[j])
        decreases s_len - start
    {
        let c = s@[start];
        if !chars_set@.contains(c) {
            break;
        }
        start += 1;
    }
    
    s.substring(start, s_len - start)
}

proof fn lemma_empty_chars_identity(original: String, result: String)
    requires
        result@ == original@,
    ensures
        result@.len() <= original@.len(),
        exists|k: int| 0 <= k <= original@.len() && result@ == original@.subrange(k, original@.len()),
        original@.len() == 0 ==> result@.len() == 0
{
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
    /* code modified by LLM (iteration 5): Fixed vector indexing and verification */
    let mut result = Vec::new();
    let chars_val = chars;
    
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let original = a[j].clone();
                let result_str = result[j].clone();
                result_str@.len() <= original@.len() &&
                (exists|k: int| 0 <= k <= original@.len() && result_str@ == original@.subrange(k, original@.len())) &&
                (original@.len() == 0 ==> result_str@.len() == 0)
            }
        decreases a.len() - i
    {
        let original = a[i].clone();
        let stripped = match chars_val {
            Some(ref ch) => strip_start(original.clone(), ch.clone()),
            None => original.clone(),
        };
        result.push(stripped);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}