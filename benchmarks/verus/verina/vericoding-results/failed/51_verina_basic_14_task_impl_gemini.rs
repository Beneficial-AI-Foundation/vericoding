// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_z(c: char) -> bool { c == 'z' || c == 'Z' }
// </vc-helpers>

// <vc-spec>
fn contains_z(s: &str) -> (result: bool)
    ensures
        result <==> exists|i: int| 0 <= i < s@.len() && (s@[i] == 'z' || s@[i] == 'Z'),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by using the correct string lemma 'lemma_substring_from_first_char_len' */
    let mut rest = s;
    loop
        invariant
            decreases rest.len(),
            exists|prefix: Seq<char>| s@ == prefix.add(rest@) && !(exists|i: int| 0 <= i < prefix.len() && is_z(prefix[i])),
    {
        if rest.is_empty() {
            return false;
        }

        let head = rest.get_char_from_codepoint_start(0);
        let tail = rest.substring_from(rest.first_char_len());

        proof {
            vstd::string::lemma_substring_from_first_char_len(rest);
        }

        if is_z(head) {
            return true;
        }

        rest = tail;
    }
}
// </vc-code>

}
fn main() {}