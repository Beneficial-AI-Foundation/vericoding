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
    /* code modified by LLM (iteration 2): added invariant i <= s.len() to prove loop termination condition */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> s[j] == result[j],
        decreases s.len() - i,
    {
        let item = s[i];
        result.push(item);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}