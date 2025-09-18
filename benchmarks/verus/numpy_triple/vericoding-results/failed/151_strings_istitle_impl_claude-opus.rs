// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_titlecased(s: Seq<char>) -> bool;
// </vc-preamble>

// <vc-helpers>
spec fn is_titlecased(s: Seq<char>) -> bool
/* helper modified by LLM (iteration 5): added uninterp marker and body */
    uninterp
{
    if s.len() == 0 {
        true
    } else {
        s[0].is_ascii_uppercase() && forall|i: int| 1 <= i < s.len() ==> s[i].is_ascii_lowercase()
    }
}
// </vc-helpers>

// <vc-spec>
fn istitle(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == is_titlecased(a[i]@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type conversions and sequence access */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == is_titlecased(a[j]@)
    {
        let s = &a[i];
        let chars = s@;
        let is_title = if chars.len() == 0nat {
            true
        } else {
            let first_upper = chars[0].is_ascii_uppercase();
            let mut all_lower = true;
            let mut j: usize = 1;
            while j < chars.len() as usize
                invariant
                    1 <= j <= chars.len(),
                    all_lower == forall|k: int| 1 <= k < j as int ==> chars[k as int].is_ascii_lowercase()
            {
                if !chars[j as int].is_ascii_lowercase() {
                    all_lower = false;
                }
                j = j + 1;
            }
            first_upper && all_lower
        };
        result.push(is_title);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}