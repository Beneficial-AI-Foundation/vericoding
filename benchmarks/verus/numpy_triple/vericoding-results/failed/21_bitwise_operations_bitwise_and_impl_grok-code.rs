// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: Vec<u8>, x2: Vec<u8>) -> (result: Vec<u8>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] as int >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] as int >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] & x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int >= 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int <= x1[i] as int,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int <= x2[i] as int,
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> (x1[i] == 0 || x2[i] == 0)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == x2[i] ==> result[i] == x1[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed invariants to include all postconditions, added bounds assertions, corrected indexing with @ for sequence view */
    let n = x1.len();
    let n_int = x1@.len();
    let mut result: Vec<u8> = Vec::new();
    let mut i = 0;
    while i as int < n_int
        invariant
            result@.len() == i as int,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == (x1@[j] & x2@[j]),
            forall|j: int| 0 <= j < result@.len() ==> result@[j] as int >= 0,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] as int <= x1@[j] as int,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] as int <= x2@[j] as int,
            forall|j: int| 0 <= j < result@.len() ==> (result@[j] == 0 <==> (x1@[j] == 0 || x2@[j] == 0)),
            forall|j: int| 0 <= j < result@.len() ==> (x1@[j] == x2@[j] ==> result@[j] == x1@[j]),
        decreases n_int - i as int
    {
        proof {
            assert(0 <= i as int < n_int);
        }
        let val = x1@[i as int] & x2@[i as int];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}