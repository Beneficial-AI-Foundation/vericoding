// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatch by using 0nat for nat comparison */
fn is_all_whitespace(s: &String) -> (result: bool)
    ensures
        result == (s@.len() > 0 && all_chars_whitespace(s@))
{
    let chars: Seq<char> = s@;
    if chars.len() == 0nat {
        false
    } else {
        all_chars_whitespace(chars)
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
    /* code modified by LLM (iteration 5): loop through array, check each string for all whitespace */
    let mut result: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_whitespace(a[j]@)),
            forall|j: int| 0 <= j < i ==> (a[j]@.len() == 0 ==> result[j] == false),
        decreases a.len() - i
    {
        let elem = &a[i];
        let is_ws = is_all_whitespace(elem);
        result.push(is_ws);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}