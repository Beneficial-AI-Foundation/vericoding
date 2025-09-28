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
    /* code modified by LLM (iteration 5): fixed bounds checking by adding explicit asserts for sequence access */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> 0 <= j < result@.len() && 0 <= j < a@.len() && 0 <= j < b@.len() && result@[j] == (a@[j] == b@[j]),
        decreases a.len() - i
    {
        assert(i < a.len());
        assert(a.len() == b.len());
        assert(i < b.len());
        assert(0 <= i < a@.len());
        assert(0 <= i < b@.len());
        let equal_at_i = a[i] == b[i];
        result.push(equal_at_i);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}