// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn split_string_into_chars(s: Vec<char>) -> (v: Vec<char>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> v[i] == s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Changed loop index 'i' to type usize to match vector API requirements for length, indexing, and arithmetic. */
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == s[j],
        decreases s.len() - i
    {
        result.push(s[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}