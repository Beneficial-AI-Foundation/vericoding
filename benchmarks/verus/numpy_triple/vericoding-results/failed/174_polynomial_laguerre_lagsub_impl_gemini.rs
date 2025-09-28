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
    /* code modified by LLM (iteration 5): fixed compilation error by using Vec::new and push */
    let len = c1.len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            c1.len() == c2.len(),
            len == c1.len(),
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == c1@[j] as int - c2@[j] as int,
        decreases len - i
    {
        let v1 = c1[i];
        let v2 = c2[i];
        let diff = v1 - v2;
        result.push(diff);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}