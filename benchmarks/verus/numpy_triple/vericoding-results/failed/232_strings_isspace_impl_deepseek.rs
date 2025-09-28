// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type mismatches and indexing */
fn all_chars_whitespace_recursive(s: Seq<char>, i: int) -> (result: bool)
    requires
        0 <= i <= s.len() as int,
    ensures
        result == all_chars_whitespace(s.subrange(i as nat, s.len() as nat)),
    decreases s.len() as int - i
{
    if i >= s.len() as int {
        true
    } else {
        is_whitespace_char(s[i as nat]) && all_chars_whitespace_recursive(s, i + 1)
    }
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
{
    /* code modified by LLM (iteration 5): Fixed indexing and type conversions */
    let mut result_vec = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            result_vec.len() == idx,
            forall|j: int| 0 <= j < idx ==> result_vec[j] == (a[j]@.len() > 0 && all_chars_whitespace(a[j]@)),
            forall|j: int| 0 <= j < idx ==> (a[j]@.len() == 0 ==> result_vec[j] == false),
        decreases a.len() - idx
    {
        let s = &a[idx];
        let chars = s@;
        let is_empty = chars.len() == 0;
        let is_whitespace = if is_empty {
            false
        } else {
            all_chars_whitespace_recursive(chars, 0)
        };
        result_vec.push(is_whitespace);
        idx = idx + 1;
    }
    
    result_vec
}
// </vc-code>

}
fn main() {}