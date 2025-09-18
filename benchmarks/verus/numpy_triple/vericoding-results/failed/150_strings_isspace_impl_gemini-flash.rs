// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary `to_usize` helper */
// </vc-helpers>

// <vc-spec>
spec fn is_whitespace_char(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'
}

spec fn all_chars_whitespace(s: Seq<char>) -> bool 
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_whitespace_char(s[0]) && all_chars_whitespace(s.skip(1))
    }
}

fn isspace(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (a[i]@.len() > 0 && all_chars_whitespace(a[i]@)),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i]@.len() == 0 ==> result[i] == false),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed ghost char indexing to use usize cast */
{
    let mut result: Vec<bool> = Vec::new();
    let a_len = a.len();
    let mut i: usize = 0;
    while i < a_len
        invariant 
            0 <= i as int <= a_len as int,
            result.len() == i,
            // all previously added results are correct
            forall|idx: int| 0 <= idx < i as int ==> 
                result[idx] == (a[idx as usize]@.len() > 0 && all_chars_whitespace(a[idx as usize]@))
    {
        // We take the string, and convert it to a Seq<char> for spec functions.
        // If `s` were `&String`, we'd take `s@` (coercion from String to Seq<char>)
        let s = a[i]@;
        let mut all_whitespace = true;
        let s_len = s.len();
        let mut k: usize = 0;
        while k < s_len
            invariant
                0 <= k as int <= s_len as int,
                all_whitespace == (forall|j: int| 0 <= j < k as int ==> is_whitespace_char(s[j as int]))
        {
            if !is_whitespace_char(s[k as usize]) { // Changed s[k as int] to s[k as usize]
                all_whitespace = false;
            }
            k = k + 1;
        }
        // Apply verification conditions.
        if s.len() == 0 {
            all_whitespace = false;
            // proof {
            //     assert(s.len() == 0 ==> all_chars_whitespace(s)); // this is true by spec
            //     assert(all_whitespace == false);
            // }
        } else {
            // proof {
            //     // The inner loop invariant provides all_whitespace == (forall|j: int| 0 <= j < s.len() ==> is_whitespace_char(s[j]))
            //     // By definition of all_chars_whitespace, this is equivalent to all_chars_whitespace(s)
            //     assert(all_whitespace == all_chars_whitespace(s));
            // }
        }
        
        result.push(all_whitespace);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}