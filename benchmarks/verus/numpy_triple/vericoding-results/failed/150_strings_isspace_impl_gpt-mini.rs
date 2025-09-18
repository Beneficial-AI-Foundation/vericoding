// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove sequence length non-negativity */
proof fn seq_len_nonneg(s: Seq<char>) ensures (s.len() as int) >= 0 { proof { assert(s.len() as int >= 0); } }
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
    /* code modified by LLM (iteration 5): iterate over vector and compute whitespace flags with proper casts and invariants */
    let mut result: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < a.len() as int {
        decreases (a.len() as int - i);
        invariant 0 <= i && i <= a.len() as int && result.len() as int == i && (forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() as int > 0 && all_chars_whitespace(a[j]@)));
        let s = a[i]@;
        let b = (s.len() as int > 0) && all_chars_whitespace(s);
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}