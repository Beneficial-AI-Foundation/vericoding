// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix nat/usize type mismatch in while condition */
fn check_all_whitespace(s: &String) -> (result: bool)
    ensures
        result == all_chars_whitespace(s@),
{
    let mut i: usize = 0;
    while i < s@.len() as usize
        invariant
            i <= s@.len(),
            forall|j: int| 0 <= j < i ==> is_whitespace_char(s@[j]),
    {
        proof {
            let ghost_i: int = i as int;
            let c = s@[ghost_i];
        }
        let c = s.as_bytes()[i] as char;
        if !is_whitespace_char(c) {
            return false;
        }
        i += 1;
    }
    true
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
    /* code modified by LLM (iteration 5): fix nat/int type mismatch in sequence length comparison */
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == (a[j]@.len() > 0 && all_chars_whitespace(a[j]@)),
            forall|j: int| 0 <= j < i ==> 
                (a[j]@.len() == 0 ==> result[j] == false),
    {
        let s = &a[i];
        let is_ws = if s@.len() == 0nat {
            false
        } else {
            check_all_whitespace(s)
        };
        result.push(is_ws);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}