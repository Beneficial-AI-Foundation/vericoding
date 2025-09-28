// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lagsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    requires c1.len() == c2.len(),
    ensures 
        result.len() == c1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == c1[i] as int - c2[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added parentheses to assertions to fix compilation parsing error */
    let mut result = Vec::new();
    let mut i = 0;
    while i < c1.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == c1[j] as int - c2[j] as int,
        decreases c1.len() - i
    {
        proof {
            assert((i as int < c1@.len()) && (i as int < c2@.len()));
            assert((c1@[i as int] as int - c2@[i as int] as int >= -128) && (c1@[i as int] as int - c2@[i as int] as int <= 127));
        }
        result.push(c1[i] - c2[i]);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}