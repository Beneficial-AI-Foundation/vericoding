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
/* code modified by LLM (iteration 5): Fixed type mismatch error `result[j as usize]` (expected `u8`, found `int`). */
{
    let len_usize = x1.len();
    let ghost len_int: nat = x1.len() as nat;
    let mut result: Vec<u8> = Vec::new();
    result.reserve(len_usize);

    let mut i: usize = 0;

    while i < len_usize
        invariant
            0 <= i,
            i <= len_usize,
            result.len() == i,
            result.capacity() >= len_usize,
            forall|j: int| 0 <= j < i as int ==> result[j as usize] == (x1[j as usize] & x2[j as usize]),
        decreases len_usize - i
    {
        result.push(x1[i] & x2[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}