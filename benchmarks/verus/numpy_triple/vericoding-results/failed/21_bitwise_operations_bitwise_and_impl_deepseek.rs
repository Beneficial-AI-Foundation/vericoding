// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed proof assertions with proper bounds and non-negative properties */
fn bitwise_and_helper(x: i32, y: i32) -> (result: i32)
    requires x >= 0, y >= 0
    ensures result == (x & y), result >= 0, result <= x, result <= y,
            result == 0 <==> (x == 0 || y == 0),
            (x == y ==> result == x)
{
    proof {
        assert(0 <= x & y);
        assert(x & y <= x);
        assert(x & y <= y);
        assert((x & y == 0) <==> (x == 0 || y == 0));
        assert(x == y ==> x & y == x);
    }
    x & y
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
/* code modified by LLM (iteration 5): Added explicit bounds checking for vector indexing and proper proof structure */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] & x2[j]),
            forall|j: int| 0 <= j < i ==> result[j] >= 0,
            forall|j: int| 0 <= j < i ==> result[j] <= x1[j],
            forall|j: int| 0 <= j < i ==> result[j] <= x2[j],
            forall|j: int| 0 <= j < i ==> (result[j] == 0 <==> (x1[j] == 0 || x2[j] == 0)),
            forall|j: int| 0 <= j < i ==> (x1[j] == x2[j] ==> result[j] == x1[j])
        decreases x1.len() - i
    {
        assert(0 <= i && i < x1.len());
        let x1_val = x1[i];
        let x2_val = x2[i];
        assert(x1_val >= 0);
        assert(x2_val >= 0);
        let and_result = bitwise_and_helper(x1_val, x2_val);
        result.push(and_result);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}