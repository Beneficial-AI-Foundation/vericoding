// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): switch to mathematical int for spec computation to fix i32/int mismatch */
spec fn invert_elem(z: int) -> int { -(z + 1) }
// </vc-helpers>

// <vc-spec>
fn invert(x: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] == -(x[i] + 1),
        forall|i: int| 0 <= i < x.len() && x[i] == 0 ==> result[i] == -1,
        forall|i: int| 0 <= i < x.len() && x[i] == -1 ==> result[i] == 0,
        forall|i: int| 0 <= i < x.len() && x[i] != -1 ==> (x[i] > 0 <==> result[i] < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement loop building inverted vector and maintain invariant tying result to spec helper */
    let n = x.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == x.len(),
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j] == invert_elem(x[j])
        decreases n - i
    {
        let xi = x[i];
        result.push(-xi - 1);
        i = i + 1;
    }
    assert(result.len() == x.len());
    result
}
// </vc-code>

}
fn main() {}