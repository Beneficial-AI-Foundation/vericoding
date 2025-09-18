// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_xor(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] ^ x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == x2[i],
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == x2[i] ==> result[i] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches by using int for index variable */
    let mut result = Vec::<i32>::new();
    let mut i: int = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result@[j] == (x1@[j] ^ x2@[j]),
            forall |j: int| 0 <= j < i ==> result@[j] >= 0,
        decreases x1.len() - i
    {
        assert(0 <= i < x1.len());
        let res = x1[i] ^ x2[i];
        assert(res >= 0);
        assert(if x1[i] == 0 { res == x2[i] } else { true });
        assert(if x2[i] == 0 { res == x1[i] } else { true });
        assert(if x1[i] == x2[i] { res == 0 } else { true });
        result.push(res);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}