// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
exec fn is_whitespace_char_exec(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'
}

proof fn is_whitespace_char_exec_equiv(c: char)
    ensures is_whitespace_char_exec(c) == is_whitespace_char(c)
{
    assert(is_whitespace_char(c) == (c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'));
}

/* helper modified by LLM (iteration 5): fixed compilation by replacing while loop with for loop to avoid using int/nat in exec code */
exec fn is_whitespace_string(s: &String) -> (result: bool)
    ensures result == (s.len() > 0 && all_chars_whitespace(s@))
{
    if s.is_empty() {
        false
    } else {
        let mut all_ws = true;
        for c in s.chars() {
            if !is_whitespace_char_exec(c) {
                all_ws = false;
                break;
            }
        }
        all_ws
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
    /* code modified by LLM (iteration 4): no changes needed, helper function was fixed instead */
    let mut result = Vec::new();
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_whitespace(a[j]@))
    {
        result.push(is_whitespace_string(&a[i]));
    }
    result
}
// </vc-code>

}
fn main() {}