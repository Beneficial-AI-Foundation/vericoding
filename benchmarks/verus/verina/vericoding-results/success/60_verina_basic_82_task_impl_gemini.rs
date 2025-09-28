// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn remove_front(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        a.len() > 0,
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i + 1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to fix termination error */
    let mut result = Vec::new();
    let mut i: usize = 1;
    while i < a.len()
        invariant
            a.len() > 0,
            1 <= i <= a.len(),
            result.len() == i - 1,
            forall|j: int| 0 <= j < result.len() ==> result.spec_index(j) == a.spec_index(j + 1),
        decreases a.len() - i
    {
        let item = a[i];
        result.push(item);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}