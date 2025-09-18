// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): moved to spec function to avoid int usage in exec code */
spec fn check_all_whitespace_spec(s: Seq<char>) -> bool {
    all_chars_whitespace(s)
}
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
/* code modified by LLM (iteration 5): fixed type mismatches by using proper int casts and sequence indexing */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == (a[j]@.len() > 0 && all_chars_whitespace(a[j]@)),
            forall|j: int| 0 <= j < i ==> 
                (a[j]@.len() == 0 ==> result[j] == false)
    {
        let is_ws = if a[i].len() == 0 {
            false
        } else {
            let mut all_ws = true;
            let mut k = 0;
            while k < a[i].len() && all_ws
                invariant
                    0 <= k <= a[i]@.len(),
                    all_ws ==> forall|idx: int| 0 <= idx < k ==> is_whitespace_char(a[i]@[idx])
            {
                if !is_whitespace_char(a[i]@[k as int]) {
                    all_ws = false;
                }
                k += 1;
            }
            all_ws && k == a[i].len()
        };
        result.push(is_ws);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}