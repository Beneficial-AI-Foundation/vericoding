// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed spec function with requires/ensures */
// </vc-helpers>

// <vc-spec>
fn iter_copy(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        s.len() == result.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] == result[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed compilation errors by removing spec function dependencies */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> s[j] == result[j],
        decreases s.len() - i,
    {
        result.push(s[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}