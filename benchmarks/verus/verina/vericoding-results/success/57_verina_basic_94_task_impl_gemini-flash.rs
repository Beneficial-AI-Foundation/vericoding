// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn iter_copy(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] == result[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            result.len() == i,
            s.len() == result.len() + (s.len() - i),
            forall|j: int| 0 <= j < i ==> s@[j] == result@[j],
            i <= s.len(),
        decreases s.len() - i
    {
        result.push(s[i]); // Fix: Use `s[i]` for runtime Vec indexing
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}