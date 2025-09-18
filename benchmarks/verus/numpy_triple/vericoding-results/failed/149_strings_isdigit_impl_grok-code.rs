// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_chars_digit(s: Seq<char>) -> bool { forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9' }
// </vc-helpers>

// <vc-spec>
spec fn all_chars_digit(s: Seq<char>) -> bool;

fn isdigit(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == (a[i]@.len() > 0 && all_chars_digit(a[i]@))
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<bool> = Vec::new();
    for s in a {
        let chars = s@;
        let len = chars.len();
        let mut is_valid = len > 0;
        for i in 0..len {
            if chars[i] < '0' || chars[i] > '9' {
                is_valid = false;
                break;
            }
        }
        result.push(is_valid);
    }
    result
}
// </vc-code>

}
fn main() {}