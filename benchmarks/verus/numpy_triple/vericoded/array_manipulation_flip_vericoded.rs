// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn numpy_flip(m: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == m.len(),
        forall|i: int| 0 <= i < m.len() ==> result[i] == m[m.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed compilation error by using usize for executable variables */
    let mut result: Vec<f32> = Vec::new();
    let n = m.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == m.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> result@[j] == m@[(n as int) - 1 - j],
        decreases n - i
    {
        let index = n - 1 - i;
        result.push(m[index]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}