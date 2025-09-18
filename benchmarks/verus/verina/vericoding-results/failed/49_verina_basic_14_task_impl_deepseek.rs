// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove problematic proof helper and add proper spec function */
spec fn is_valid_char(c: char) -> bool {
    c == 'z' || c == 'Z'
}
// </vc-helpers>

// <vc-spec>
fn contains_z(s: &str) -> (result: bool)
    ensures
        result <==> exists|i: int| 0 <= i < s@.len() && (s@[i] == 'z' || s@[i] == 'Z'),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix type conversion and avoid direct int usage */
    let mut i: usize = 0;
    let s_seq = s@;
    let len: usize = s_seq.len();
    while i < len
        invariant
            i <= len,
            forall|j: int| 0 <= j < i as int ==> !(s_seq[j] == 'z' || s_seq[j] == 'Z'),
    {
        let c = s_seq[i as int];
        if c == 'z' || c == 'Z' {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}