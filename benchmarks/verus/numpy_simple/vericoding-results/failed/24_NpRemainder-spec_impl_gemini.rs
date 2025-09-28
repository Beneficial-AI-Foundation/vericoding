// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remainder(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed syntax error in proof block */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            forall|k: int| 0 <= k < b.len() ==> b@[k] != 0,
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] % b@[j],
        decreases a.len() - i
    {
        assert(b[i] != 0);
        let rem = a[i] % b[i];

        result.push(rem);

        proof {
            assert(result@[i as int] == rem);
            assert forall|j: int| 0 <= j < i implies result@[j] == old(result)@[j] by {};
        }

        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}