// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): defining spec fn all_chars_digit with body to enable verification */
spec fn all_chars_digit(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i].is_ascii_digit()
}
// </vc-helpers>

// <vc-spec>
spec fn all_chars_digit(s: Seq<char>) -> bool;

fn isdigit(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i as int] == (a[i as int]@.len() > 0 && all_chars_digit(a[i as int]@))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): implementing the isdigit function with loop to manually verify character digits */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i as nat,
            forall|k: int| 0 <= k < i ==> result[k as int] == (a[k as int]@.len() > 0 && all_chars_digit(a[k as int]@)),
        decreases a.len() - i
    {
        let s = &a[i];
        let len = s.len();
        let mut all_digit = true;
        if len == 0 {
            all_digit = false;
        } else {
            let mut j: usize = 0;
            while j < len
                invariant
                    0 <= j <= len,
                    all_digit ==> forall|k: int| 0 <= k < j ==> s@[k].is_ascii_digit(),
                decreases len - j
            {
                if !s[j].is_ascii_digit() {
                    all_digit = false;
                    break;
                }
                j += 1;
            }
        }
        result.push(all_digit);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}