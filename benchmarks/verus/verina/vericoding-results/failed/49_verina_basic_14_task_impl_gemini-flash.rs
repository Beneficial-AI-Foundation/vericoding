// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_z(s: &str) -> (result: bool)
    ensures
        result <==> exists|i: int| 0 <= i < s@.len() && (s@[i] == 'z' || s@[i] == 'Z'),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Remove `.view()` call from `s_seq` as it is already a `Seq<char>` and directly use `@` for indexing */
{
    let s_seq = s.view();
    let mut i: nat = 0;
    while i < s_seq.len()
        invariant
            0 <= i,
            i <= s_seq.len(),
            forall|j: nat| 0 <= j < i ==> !(s_seq@[j] == 'z' || s_seq@[j] == 'Z'),
        decreases s_seq.len() - i
    {
        if s_seq@[i] == 'z' || s_seq@[i] == 'Z' {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}