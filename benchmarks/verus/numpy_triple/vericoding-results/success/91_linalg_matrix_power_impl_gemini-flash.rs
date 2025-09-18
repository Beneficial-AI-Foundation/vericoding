// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added decreases clauses to loops */
fn create_identity_matrix(size: usize) -> Vec<Vec<f32>> {
    let mut mat = Vec::with_capacity(size);
    let mut i = 0;
    while i < size 
        decreases size - i
    {
        let mut row = Vec::new();
        let mut j = 0;
        while j < size
            decreases size - j
        {
            if i == j {
                row.push(1.0);
            } else {
                row.push(0.0);
            }
            j = j + 1;
        }
        mat.push(row);
        i = i + 1;
    }
    mat
}
// </vc-helpers>

// <vc-spec>
fn matrix_power(a: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        a.len() > 0,
        forall|i: int| #![trigger a[i]] 0 <= i < a.len() ==> a[i].len() == a.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> result[i].len() == a.len(),
        true, // Result matrix elements exist (trivially true)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Returned `a` as the result for power 1 */
{
    a
}
// </vc-code>

}
fn main() {}