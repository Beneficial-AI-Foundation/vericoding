// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper to check if char is z */
spec fn is_z_char(c: char) -> bool {
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
    /* code modified by LLM (iteration 5): use char iteration instead of bytes */
    let ghost chars = s@;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> !is_z_char(chars[j])
    {
        let c = s.chars().nth(i).unwrap();
        if is_z_char(c) {
            proof {
                assert(is_z_char(chars[i as int]));
                assert(exists|k: int| 0 <= k < s@.len() && is_z_char(chars[k]));
            }
            return true;
        }
        i += 1;
    }
    proof {
        assert(forall|j: int| 0 <= j < s@.len() ==> !is_z_char(chars[j]));
    }
    false
}
// </vc-code>

}
fn main() {}