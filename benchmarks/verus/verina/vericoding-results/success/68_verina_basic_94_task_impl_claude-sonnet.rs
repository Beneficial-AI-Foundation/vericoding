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
    /* code modified by LLM (iteration 2): added decreases clause to fix verification error */
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> s[j] == result[j],
        decreases s.len() - i
    {
        result.push(s[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}