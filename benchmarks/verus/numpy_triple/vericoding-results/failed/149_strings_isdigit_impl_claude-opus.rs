// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed nat comparison by casting to nat */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_digit(a[j]@))
    {
        let s = &a[i];
        let mut is_digit = s@.len() > 0nat;
        if is_digit {
            let chars = s.chars().collect::<Vec<char>>();
            let mut j = 0;
            while j < chars.len()
                invariant
                    0 <= j <= chars.len(),
                    is_digit == (j == 0 || (j > 0 && forall|k: int| 0 <= k < j ==> chars[k].is_ascii_digit()))
            {
                if !chars[j].is_ascii_digit() {
                    is_digit = false;
                    break;
                }
                j = j + 1;
            }
            if j == chars.len() {
                assert(forall|k: int| 0 <= k < chars@.len() ==> chars@[k].is_ascii_digit());
                assert(chars@.len() == s@.len());
            }
        }
        result.push(is_digit);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}