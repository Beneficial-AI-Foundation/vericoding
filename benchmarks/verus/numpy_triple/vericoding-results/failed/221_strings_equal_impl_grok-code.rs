// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i as int] == (x1[i as int] == x2[i as int]),
        forall|i: int| 0 <= i < result.len() ==> (result[i as int] == true <==> x1[i as int] == x2[i as int]),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i as int] == true,
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): Use sequence views for comparisons in loop to avoid indexing errors */
    let len = x1@.len() as int;
    let x1_seq = x1@;
    let x2_seq = x2@;
    let mut result = Vec::with_capacity(len as usize);
    let mut i = 0;
    while i < len
        invariant
            i <= len,
            result.len() == (i as usize),
            forall|j: int| 0 <= j < i ==> result@[j] == (x1_seq@j == x2_seq@j),
        decreases len - i
    {
        result.push(x1_seq[i] == x2_seq[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}