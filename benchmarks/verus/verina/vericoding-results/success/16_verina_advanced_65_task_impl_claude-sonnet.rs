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
    let mut result = Vec::new();
    let mut i = s.len();
    
    while i > 0
        invariant
            result@.len() == s@.len() - i,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == s@[s@.len() - 1 - j],
        decreases i
    {
        i = i - 1;
        result.push(s[i]);
    }
    
    result
}
// </vc-code>

}
fn main() {}