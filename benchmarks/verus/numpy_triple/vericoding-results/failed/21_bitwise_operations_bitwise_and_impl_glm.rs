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
    /* code modified by LLM (iteration 3): fixed type of index variable i from usize to int and adjusted vector length conversions */
    let mut result = Vec::with_capacity(x1.len());
    let mut i: int = 0;
    while i < (x1.len() as int)
        invariant
            0 <= i <= x1.len() as int,
            result.len() as int == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] & x2[j]),
            forall|j: int| 0 <= j < i ==> result[j] as int >= 0,
            forall|j: int| 0 <= j < i ==> result[j] as int <= x1[j] as int,
            forall|j: int| 0 <= j < i ==> result[j] as int <= x2[j] as int,
            forall|j: int| 0 <= j < i ==> (result[j] == 0 <==> (x1[j] == 0 || x2[j] == 0)),
            forall|j: int| 0 <= j < i ==> (x1[j] == x2[j] ==> result[j] == x1[j]),
        decreases (x1.len() as int) - i
    {
        result.push(x1[i] & x2[i]);
        proof {
            let a = x1[i];
            let b = x2[i];
            let r = result[i];
            assert(r as int >= 0);
            assert(r as int <= a as int);
            assert(r as int <= b as int);
            assert((r == 0) <==> (a == 0 || b == 0));
            if a == b {
                assert(r == a);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}