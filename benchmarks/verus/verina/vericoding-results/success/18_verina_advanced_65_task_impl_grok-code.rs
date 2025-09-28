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
    /* code modified by LLM (iteration 2): fixed type mismatches by using usize instead of int for indexing */
    let mut i: usize = s.len();
    let mut result = Vec::<char>::new();
    while i > 0
        invariant
            result@.len() == s@.len() - i as nat,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == s@[s@.len() - 1 - j]
        decreases i
    {
        i -= 1;
        result.push(s[i]);
    }
    result
}
// </vc-code>

}
fn main() {}