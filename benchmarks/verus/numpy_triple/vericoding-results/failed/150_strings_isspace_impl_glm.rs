// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed nat suffix syntax error */
fn is_whitespace_char_exec(c: char) -> (b: bool) ensures b == is_whitespace_char(c) {
    c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'
}

/* helper modified by LLM (iteration 5): fixed nat suffix syntax error */
fn is_all_whitespace(s: String) -> (b: bool) ensures b == (s@.len() > 0 && all_chars_whitespace(s@)) {
    if s@.len() == 0 {
        false
    } else {
        let mut all_white = true;
        for c in s.chars() {
            if !is_whitespace_char_exec(c) {
                all_white = false;
                break;
            }
        }
        all_white
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
    /* code modified by LLM (iteration 5): no changes needed, helper function fixed in vc-helpers */
    let mut result = Vec::new();
    for s in a {
        let b = is_all_whitespace(s);
        result.push(b);
    }
    result
}
// </vc-code>

}
fn main() {}