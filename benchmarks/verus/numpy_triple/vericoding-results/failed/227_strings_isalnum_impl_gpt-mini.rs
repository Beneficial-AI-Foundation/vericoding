// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define is_alphanumeric_char */
spec fn is_alphanumeric_char(c: char) -> bool {
    (c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')
}

/* helper modified by LLM (iteration 5): lemma that empty sequence is alphanumeric */
proof fn all_chars_alphanumeric_empty()
    ensures
        all_chars_alphanumeric(Seq::<char>::empty()),
{
    // By definition of all_chars_alphanumeric, empty sequence yields true
}

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
    /* code modified by LLM (iteration 5): compute per-string alphanumeric flags using usize index and Seq.len() */
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            res.len() == i,
            forall|j: nat| j < i ==> res[j] == (a[j]@.len() > 0 && all_chars_alphanumeric(a[j]@)),
        decreases a.len() - i
    {
        let s: Seq<char> = a[i]@;
        let flag: bool = (s.len() > 0) && all_chars_alphanumeric(s);
        res.push(flag);
        i += 1;
    }

    res
}
// </vc-code>

}
fn main() {}