// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn reverse_string(s: &Vec<char>) -> (result: Vec<char>)
    ensures
        result@.len() == s@.len(),
        forall|i: int| 0 <= i < s@.len() ==> result@[i] == s@[s@.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation error by using correct vector indexing syntax */
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    let len = s.len();
    while i < len
        invariant
            i <= len,
            s@.len() == len,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == s@[len - 1 - j],
        decreases len - i,
    {
        let char_to_add = s[len - 1 - i];
        result.push(char_to_add);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}