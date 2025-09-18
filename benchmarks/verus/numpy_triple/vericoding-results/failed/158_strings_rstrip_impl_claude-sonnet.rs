// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn should_remove_char(c: char, chars_opt: Option<String>) -> bool {
    match chars_opt {
        Some(chars) => chars@.contains(c),
        None => c == ' ' || c == '\t' || c == '\n' || c == '\r'
    }
}

/* helper modified by LLM (iteration 5): moved nat conversion to proof block */
fn rstrip_string(s: String, chars: Option<String>) -> (result: String)
    ensures result@.len() <= s@.len()
{
    let mut end: usize = s@.len();
    while end > 0
        invariant 0 <= end <= s@.len()
    {
        proof {
            let end_nat: nat = (end - 1) as nat;
            let last_char = s@.index(end_nat);
            assert(should_remove_char(last_char, chars));
        }
        let last_char_index = end - 1;
        let ghost last_char: char = s@.index(last_char_index as nat);
        if should_remove_char(last_char, chars) {
            end = end - 1;
        } else {
            break;
        }
    }
    s.substring_char(0, end).to_string()
}
// </vc-helpers>

// <vc-spec>
fn rstrip(a: Vec<String>, chars: Option<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() <= a[i]@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed ghost variable usage */
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j]@.len() <= a[j]@.len()
    {
        let stripped = rstrip_string(a[i].clone(), chars.clone());
        result.push(stripped);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}