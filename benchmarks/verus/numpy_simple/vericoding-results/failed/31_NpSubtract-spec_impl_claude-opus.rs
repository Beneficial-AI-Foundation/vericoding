// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn subtract(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result@[i] == a@[i] - b@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut result = Vec::new();
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            i == result.len(),
            n == a.len(),
            n == b.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] - b@[j],
        decreases n - i
    {
        let diff = a[i] - b[i];
        result.push(diff);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}