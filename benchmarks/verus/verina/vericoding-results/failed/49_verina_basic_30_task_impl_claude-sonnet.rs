// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): moved length equality assertion before loop and removed redundant assertions */
    let mut result = Vec::new();
    assert(a.len() == b.len());
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> 0 <= j < a.len() && 0 <= j < b.len() && result[j] == a[j] % b[j],
        decreases a.len() - i
    {
        result.push(a[i] % b[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}