// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The previous helper section was empty, so it's kept empty. */
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
/* code modified by LLM (iteration 5): Replaced `substring` with `substring_char` where it applies to fix compilation errors due to method name mismatch. */
{
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let original = #[trigger] a[j];
                let result_str = #[trigger] result[j];
                result_str@.len() <= original@.len() &&
                (exists|k: int| 0 <= k <= original@.len() as int && 
                 result_str@ == original@.subrange(k, original@.len() as int)) &&
                (original@.len() == 0 ==> result_str@.len() == 0)
            },
    {
        let s = &a[i];
        let stripped_s: String;

        match &chars {
            Some(char_set_str) => {
                let char_set_vec: Vec<char> = char_set_str.chars().collect();
                let mut start_index = 0;
                while start_index < s.len() {
                    // Use `usize` for runtime indexing if `get_char` is a runtime operation
                    let char_at_index = s.chars().nth(start_index).unwrap();
                    if char_set_vec.contains(&char_at_index) {
                        start_index = start_index + 1;
                    } else {
                        break;
                    }
                }
                stripped_s = s.substring_char(start_index, s.len()).to_string();
            }
            None => {
                let mut start_index = 0;
                while start_index < s.len() {
                    // Use `usize` for runtime indexing if `get_char` is a runtime operation
                    let char_at_index = s.chars().nth(start_index).unwrap();
                    if char_at_index.is_whitespace() {
                        start_index = start_index + 1;
                    } else {
                        break;
                    }
                }
                stripped_s = s.substring_char(start_index, s.len()).to_string();
            }
        }

        result.push(stripped_s);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}