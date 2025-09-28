// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide executable whitespace check consistent with spec */
fn is_whitespace_char_exec(c: char) -> (result: bool)
    ensures
        result == is_whitespace_char(c),
{
    c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'
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
    /* code modified by LLM (iteration 2): avoid ghost nat/int in exec code; build result with an exec loop */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            0 <= i as int <= a.len() as int,
        decreases a.len() as int - i as int
    {
        let s_ref = &a[i];
        let b = s_ref.len() > 0; // placeholder: will be strengthened in next iterations
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}