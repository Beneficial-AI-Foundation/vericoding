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
    /* code modified by LLM (iteration 2): Adding decreases clause to the while loop and correcting loop invariant for result.len() */
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == 1,
            forall|j: int| 0 <= j < i ==> result[j] as int > 0,
            forall|j: int, k: int| 0 <= j < i && 0 <= k < i ==> result[j] == result[k],
        decreases (n - i)
    {
        result.push(1);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}