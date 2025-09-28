// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_flatiter(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added decreases clause to while loop */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j],
            i <= a.len(),
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}