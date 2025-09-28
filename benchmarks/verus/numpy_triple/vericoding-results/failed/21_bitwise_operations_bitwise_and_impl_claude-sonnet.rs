// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): helper function for bitwise and properties with correct int parameters */
fn bitwise_and_properties(a: int, b: int)
    requires
        0 <= a <= 255,
        0 <= b <= 255,
    ensures
        (a & b) >= 0,
        (a & b) <= a,
        (a & b) <= b,
        ((a & b) == 0 <==> (a == 0 || b == 0)),
        (a == b ==> (a & b) == a),
{
    // Properties of bitwise AND follow from the definition
}
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
    /* code modified by LLM (iteration 5): fixed type mismatch by casting to int for helper function */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] & x2[j]),
            forall|j: int| 0 <= j < i ==> result[j] as int >= 0,
            forall|j: int| 0 <= j < i ==> result[j] as int <= x1[j] as int,
            forall|j: int| 0 <= j < i ==> result[j] as int <= x2[j] as int,
            forall|j: int| 0 <= j < i ==> (result[j] == 0 <==> (x1[j] == 0 || x2[j] == 0)),
            forall|j: int| 0 <= j < i ==> (x1[j] == x2[j] ==> result[j] == x1[j]),
        decreases x1.len() - i
    {
        proof {
            assert(i < x1.len());
            assert(i < x2.len());
            bitwise_and_properties(x1[i] as int, x2[i] as int);
        }
        let and_result = x1[i] & x2[i];
        result.push(and_result);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}