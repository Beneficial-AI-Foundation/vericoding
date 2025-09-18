// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): provides a single equivalence lemma for whitespace checks */
proof fn lemma_all_whitespace_equivalence(s: Seq<char>)
    ensures all_chars_whitespace(s) <==> (forall|i: int| 0 <= i < s.len() ==> is_whitespace_char(s[i]))
    decreases s.len()
{
    if s.len() > 0 {
        lemma_all_whitespace_equivalence(s.skip(1));
    }
}

/* helper modified by LLM (iteration 5): fixed unsupported String::len and String::get_char */
fn check_all_whitespace(s: &String) -> (result: bool)
    ensures result == all_chars_whitespace(s@)
{
    let mut i: usize = 0;
    while i < s@.len()
        invariant
            0 <= i <= s@.len(),
            forall|j: int| 0 <= j < i as int ==> is_whitespace_char(s@[j]),
    {
        let c = s@[i as int];
        if !is_whitespace_char(c) {
            proof {
                lemma_all_whitespace_equivalence(s@);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        lemma_all_whitespace_equivalence(s@);
    }
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
    /* code modified by LLM (iteration 5): fixed unsupported String::len */
    let ghost original_a = a@;
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@ == original_a,
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> 
                result[j] == (a[j]@.len() > 0 && all_chars_whitespace(a[j]@)),
    {
        let s = &a[i];
        let b = if s@.len() > 0 {
            check_all_whitespace(s)
        } else {
            false
        };
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}