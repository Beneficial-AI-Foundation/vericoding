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
    /* code modified by LLM (iteration 2): added decreases clause to loop */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> result[k] as int == 1,
        decreases n - i
    {
        result.push(1i8);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}