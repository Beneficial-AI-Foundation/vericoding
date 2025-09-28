// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix indexing into Seq<String> and use String view */
spec fn isalnum_result_seq(a: Seq<String>) -> Seq<bool>
{
    Seq::new(a.len(), |i: int| {
        let s = a[i]@;
        s.len() > 0 && all_chars_alphanumeric(s)
    })
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
    /* code modified by LLM (iteration 5): construct result from spec sequence using Vec::from_spec_seq */
    let ghost seq_res: Seq<bool> = isalnum_result_seq(a@);
    let result: Vec<bool> = Vec::from_spec_seq(seq_res);
    result
}
// </vc-code>

}
fn main() {}