// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ones(n: usize) -> (result: Vec<i8>)
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < n ==> result[i] as int == 1,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n ==> result[i] == result[j],
        forall|i: int| 0 <= i < n ==> result[i] as int > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop to ensure termination */
    let mut result: Vec<i8> = Vec::new();
    while result.len() < n
        invariant
            result.len() <= n,
            forall|i: int| 0 <= i < result.len() ==> result[i] as int == 1,
        decreases n - result.len()
    {
        result.push(1);
    }
    result
}
// </vc-code>


}
fn main() {}