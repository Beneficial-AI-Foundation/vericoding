// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn unique_sorted(s: Vec<i8>) -> (result: Vec<i8>)
    requires 
        forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] <= s@[j],
    ensures 
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result@[i] < result@[j],
        forall|x: i8| result@.contains(x) ==> s@.contains(x),
        forall|x: i8| s@.contains(x) ==> result@.contains(x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added trigger annotation to fix quantifier trigger inference */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            i < s.len() >= 0, /* since s.len() is int, but ghost */
            #[trigger(result@[j])] forall|j: int| 0 <= j < result@.len() - 1 ==> result@[j] < result@[j + 1],
            forall|j: int| 0 <= j < result@.len() ==> s@.contains(result@[j]),
            forall|k: int| 0 <= k < i ==> result@.contains(s@[k]),
        decreases s.len() - i
    {
        if result.len() == 0 || s[i] > result[result.len() - 1] {
            result.push(s[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}

fn main() {}