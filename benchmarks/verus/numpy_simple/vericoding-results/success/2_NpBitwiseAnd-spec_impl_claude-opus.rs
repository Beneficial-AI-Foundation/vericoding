// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_and(a: Vec<u8>, b: Vec<u8>) -> (result: Vec<u8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (a[i] & b[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut result = Vec::new();
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a.len(),
            n == b.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j] & b[j]),
        decreases n - i
    {
        let val = a[i] & b[i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}