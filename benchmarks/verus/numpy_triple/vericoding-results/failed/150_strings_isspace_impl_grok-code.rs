// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed syntax error in invariants by adding curly braces and ensuring proper spacing """
    let mut result = Vec::new();
    let mut i = 0;
    let ghost spec_a = a@;
    while i < a.len()
        invariant result.len() == i
        invariant forall |j: int| { 0 <= j < i ==> result@[j] == (spec_a[j].len() > 0 && all_chars_whitespace(spec_a[j])) }
        invariant forall |j: int| { 0 <= j < i ==> (spec_a[j].len() == 0 ==> result@[j] == false) }
        decreases a.len() - i
    {
        let is_space = if a[i]@.len() == 0 { false } else { all_chars_whitespace(a[i]@) };
        result.push(is_space);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}