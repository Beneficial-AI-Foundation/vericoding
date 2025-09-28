// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn multiply(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == (x1[i] as int) * (x2[i] as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [cast `j` to `usize` for indexing within the `for all` clause] */
{
    let mut result: Vec<i8> = Vec::new();
    let len = x1.len();
    let mut i: usize = 0;

    while i < len
        invariant
            result.len() == i,
            len == x1.len(),
            forall|j: int| 0 <= j < i ==> result[j as usize] as int == (x1[j as usize] as int * x2[j as usize] as int),
            i <= len,
        decreases len - i
    {
        let val1 = x1.get(i).unwrap();
        let val2 = x2.get(i).unwrap();
        let product = (val1 as i16 * val2 as i16) as i8; // Cast to i16 to prevent overflow during multiplication, then downcast to i8
        result.push(product);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}