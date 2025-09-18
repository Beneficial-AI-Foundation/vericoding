// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed undeclared lifetime character */
spec fn rstrip_single_string(s: String, chars: Option<String>) -> (result: String)
    ensures
        result.len() <= s.len()
{
    let s_len = s.len() as int;
    if s_len == 0 {
        String::new()
    } else {
        match chars {
            Some(c_str) => {
                let c_vec = Seq::new(c_str.len() as nat, |j: int| c_str.get_char(j as nat));
                let mut k: int = s_len - 1;
                while k >= 0 && c_vec.contains(s.get_char(k as nat))
                    invariant
                        -1 <= k < s_len,
                        c_vec.len() == c_str.len()
                {
                    k = k - 1;
                }
                s.substring(0, k + 1)
            }
            None => {
                let whitespace_chars: Seq<char> = [' ', '	', '
', ''].to_seq();
                let mut k: int = s_len - 1;
                while k >= 0 && whitespace_chars.contains(s.get_char(k as nat))
                   invariant
                        -1 <= k < s_len
                {
                    k = k - 1;
                }
                s.substring(0, k + 1)
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn rstrip(a: Vec<String>, chars: Option<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() <= a[i]@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added empty string handling to fix `index` out of bounds when original_string is empty */
{
    let mut result: Vec<String> = Vec::new();
    result.reserve(a.len());

    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j]@.len() <= a[j]@.len()
    {
        let original_string_ref = a.index(i);
        let original_string = original_string_ref.clone();
        let processed_string = rstrip_single_string(original_string, chars.clone());
        result.push(processed_string);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}