// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed compilation errors by using correct Verus string API */
fn is_whitespace_char_exec(c: char) -> (b: bool)
    ensures b == is_whitespace_char(c),
{
    c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'
}

#[verifier::spinoff_prover]
proof fn lemma_all_chars_whitespace_is_forall(s: Seq<char>)
    ensures all_chars_whitespace(s) <==> (forall|i: int| 0 <= i < s.len() ==> is_whitespace_char(s[i])),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_all_chars_whitespace_is_forall(s.skip(1));
    }
}

fn string_is_whitespace(s: &String) -> (result: bool)
    ensures result == (s@.len() > 0 && all_chars_whitespace(s@)),
{
    if s.len() == 0 {
        return false;
    }

    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.is_char_boundary(i),
            all_chars_whitespace(s.substring_view(0, i)),
        decreases s.len() - i
    {
        let c = s.get_char(i);
        if !is_whitespace_char_exec(c) {
            proof { lemma_all_chars_whitespace_is_forall(s@); }
            return false;
        }
        i = s.next_char(i);
    }
    
    proof { lemma_all_chars_whitespace_is_forall(s@); }
    return true;
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
    /* code modified by LLM (iteration 3): no changes, logic is correct and depends on helpers */
    let mut result: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == (a[j]@.len() > 0 && all_chars_whitespace(a[j]@)),
        decreases a.len() - i
    {
        let s = &a[i];
        let is_ws = string_is_whitespace(s);
        result.push(is_ws);
        i = i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}