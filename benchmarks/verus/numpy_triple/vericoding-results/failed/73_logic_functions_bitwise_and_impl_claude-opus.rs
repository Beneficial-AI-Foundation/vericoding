// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: &Vec<u32>, x2: &Vec<u32>) -> (result: Vec<u32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == (x1[i] & x2[i]) &&

            (x1[i] & x2[i]) == (x2[i] & x1[i]) &&

            (x1[i] & 0) == 0 &&

            (x1[i] & x1[i]) == x1[i] &&

            result[i] <= x1[i] && result[i] <= x2[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by using usize indexing instead of int casting */
{
    let mut result: Vec<u32> = Vec::new();
    let n = x1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == x1.len(),
            n == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] & x2[j]),
            forall|j: int| 0 <= j < i ==> (x1[j] & x2[j]) == (x2[j] & x1[j]),
            forall|j: int| 0 <= j < i ==> (x1[j] & 0) == 0,
            forall|j: int| 0 <= j < i ==> (x1[j] & x1[j]) == x1[j],
            forall|j: int| 0 <= j < i ==> result[j] <= x1[j] && result[j] <= x2[j]
        decreases n - i
    {
        let val = x1[i] & x2[i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}