// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define alphanumeric predicate */
spec fn is_alphanumeric_char(c: char) -> bool { ('0' <= c && c <= '9') || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') }
// </vc-helpers>

// <vc-spec>
spec fn is_alphanumeric_char(c: char) -> bool;

spec fn all_chars_alphanumeric(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_alphanumeric_char(s[0]) && all_chars_alphanumeric(s.skip(1))
    }
}

fn isalnum(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (a[i]@.len() > 0 && all_chars_alphanumeric(a[i]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate over strings and check non-empty and all chars alphanumeric */
    let mut result: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < a.len()
        invariant 0 <= i && i <= a.len();
        invariant result.len() == i;
        invariant forall|j: int| 0 <= j && j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_alphanumeric(a[j]@));
        decreases a.len() - i
    {
        let s = a[i]@;
        let b = s.len() > 0 && all_chars_alphanumeric(s);
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}