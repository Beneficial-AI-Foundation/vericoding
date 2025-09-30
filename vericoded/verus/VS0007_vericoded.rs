// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_xor(a: Vec<u8>, b: Vec<u8>) -> (result: Vec<u8>)
    requires 
        a.len() == b.len(),
        a.len() > 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == a@[i] ^ b@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added bounds checking assertions */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> 0 <= j < a@.len() && 0 <= j < b@.len() && result@[j] == a@[j] ^ b@[j],
        decreases a.len() - i
    {
        assert(i < a.len());
        assert(a.len() == b.len());
        assert(i < b.len());
        result.push(a[i] ^ b[i]);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}