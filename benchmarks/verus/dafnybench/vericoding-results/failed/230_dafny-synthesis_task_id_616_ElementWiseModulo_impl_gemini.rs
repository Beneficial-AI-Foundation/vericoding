// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used spec sequences in invariants and added an assertion to help prove the result invariant. */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            forall|j: int| 0 <= j < b@.len() ==> b@[j] != 0,
            (i as nat) <= a@.len(),
            result@.len() == (i as nat),
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == a@[j] % b@[j],
        decreases a.len() - i
    {
        let val = a[i] % b[i];
        result.push(val);
        assert(result@[i as int] == a@[i as int] % b@[i as int]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}