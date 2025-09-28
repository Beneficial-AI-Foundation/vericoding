// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == x1[i] as int + x2[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix bounds checking and overflow issues */
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            result.len() == i,
            i <= x1.len(),
            i <= x2.len(),
            forall|j: int| 0 <= j < i ==> result@[j] as int == x1@[j] as int + x2@[j] as int,
        decreases x1.len() - i
    {
        proof {
            assert(i < x1.len());
            assert(i < x2.len());
            assert(x1@[i as int] as int + x2@[i as int] as int >= -256);
            assert(x1@[i as int] as int + x2@[i as int] as int <= 254);
        }
        let sum = x1[i] as i16 + x2[i] as i16;
        result.push(sum as i8);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}