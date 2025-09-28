// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn equal(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<bool>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == (a@[i] == b@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix sequence bounds and add length invariants */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            a@.len() == a.len(),
            b@.len() == b.len(),
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (a@[j] == b@[j]),
        decreases a.len() - i
    {
        result.push(a[i] == b[i]);
        i += 1;
    }
    proof {
        assert(a@.len() == a.len());
        assert(b@.len() == b.len());
    }
    result
}
// </vc-code>


}
fn main() {}