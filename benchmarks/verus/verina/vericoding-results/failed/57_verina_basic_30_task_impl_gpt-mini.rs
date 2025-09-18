// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): returns element-wise modulo for int index */
fn elem_mod(a: &Vec<i32>, b: &Vec<i32>, i: int) -> (result: i32)
    requires
        0 <= i,
        i < a.len(),
        a.len() == b.len(),
        b[i] != 0,
    ensures
        result == a[i] % b[i],
{
    a[i] % b[i]
}
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
/* code modified by LLM (iteration 5): build vector of element-wise modulo using elem_mod with int indexing */
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] % b[j],
        decreases a.len() - i
    {
        let v = elem_mod(a, b, i);
        result.push(v);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}