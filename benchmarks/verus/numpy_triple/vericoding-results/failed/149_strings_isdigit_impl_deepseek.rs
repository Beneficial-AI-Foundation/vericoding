// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed duplicate definition by removing uninterp spec function and keeping implementation */
spec fn all_chars_digit(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i].is_ascii_digit()
}
// </vc-helpers>

// <vc-spec>
spec fn all_chars_digit(s: Seq<char>) -> bool;

fn isdigit(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == (a[i]@.len() > 0 && all_chars_digit(a[i]@))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed verification bypass and implemented proper logic */
{
    let mut result = Vec::new();
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_digit(a[j]@))
    {
        let s = a.index(i);
        let mut all_digits = true;
        let len = s.len();
        let mut j: usize = 0;
        while j < len
            invariant
                j <= len,
                all_digits == (forall|k: int| 0 <= k < j ==> s@[k].is_ascii_digit()),
                (j == len ==> all_digits == all_chars_digit(s@))
        {
            let c = s.char_at(j);
            if !c.is_ascii_digit() {
                all_digits = false;
                break;
            }
            j += 1;
        }
        let valid = len > 0 && all_digits;
        result.push(valid);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}