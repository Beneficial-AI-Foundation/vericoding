// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Used #[verifier(bit_vector)] to prove bitwise properties, which fixes compilation errors. */
#[verifier(bit_vector)]
proof fn lemma_bitwise_and_props(a: i32, b: i32)
    requires a >= 0, b >= 0
    ensures
        (a & b) >= 0,
        (a & b) <= a,
        (a & b) <= b,
        (a == b) ==> (a & b) == a,
        (a == 0 || b == 0) ==> (a & b) == 0,
{
}
// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] & x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x1[i],
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x2[i],
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> (x1[i] == 0 || x2[i] == 0)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == x2[i] ==> result[i] == x1[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): The implementation logic is correct; fixing the helper function resolves the compilation error. */
    let mut result: Vec<i32> = Vec::with_capacity(x1.len());
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == (x1[j] & x2[j]),
            forall|j: int| 0 <= j < i as int ==> result[j] >= 0,
            forall|j: int| 0 <= j < i as int ==> result[j] <= x1[j],
            forall|j: int| 0 <= j < i as int ==> result[j] <= x2[j],
            forall|j: int| 0 <= j < i as int ==> (result[j] == 0 <==> (x1[j] == 0 || x2[j] == 0)),
            forall|j: int| 0 <= j < i as int ==> (x1[j] == x2[j] ==> result[j] == x1[j]),
        decreases x1.len() - i
    {
        let val1 = x1[i];
        let val2 = x2[i];
        let res = val1 & val2;

        proof {
            lemma_bitwise_and_props(val1, val2);
        }

        result.push(res);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}