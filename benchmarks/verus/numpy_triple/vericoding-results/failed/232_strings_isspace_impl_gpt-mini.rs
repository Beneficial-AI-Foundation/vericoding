// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): seq is nonempty and all whitespace */
spec fn seq_is_nonempty_whitespace(s: Seq<char>) -> bool {
    s.len() != 0 && all_chars_whitespace(s)
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
    /* code modified by LLM (iteration 5): iterate over Vec<String> and determine whitespace by checking empty vs all_chars_whitespace */
    let mut result: Vec<bool> = Vec::<bool>::new();
    let mut i: usize = 0usize;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
        decreases
            a.len() - i
    {
        let s_seq: Seq<char> = a[i]@;
        let is_space: bool = if s_seq.len() == 0 { false } else { all_chars_whitespace(s_seq) };
        result.push(is_space);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}