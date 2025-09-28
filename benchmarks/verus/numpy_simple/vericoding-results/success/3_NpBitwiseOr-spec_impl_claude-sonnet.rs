// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_or(a: Vec<u8>, b: Vec<u8>) -> (result: Vec<u8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as u32 == (a[i] as u32 | b[i] as u32),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed bounds checking by ensuring i < a.len() and i < b.len() */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> 0 <= j < a.len() && 0 <= j < b.len() && result[j] as u32 == (a[j] as u32 | b[j] as u32),
        decreases a.len() - i
    {
        let or_val = a[i] | b[i];
        result.push(or_val);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}