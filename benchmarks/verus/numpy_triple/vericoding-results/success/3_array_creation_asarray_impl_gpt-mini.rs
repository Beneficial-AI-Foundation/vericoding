// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): copy elements from input Vec into a fresh Vec while keeping specs using int indices */
fn copy_vec(a: Vec<f32>) -> (res: Vec<f32>)
    requires a.len() > 0,
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < (res.len() as int) ==> res[i] == a[i],
{
    let mut res: Vec<f32> = Vec::new();
    res.reserve(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= (i as int),
            i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> res[j] == a[j],
        decreases (a.len() as int) - (i as int),
    {
        res.push(a[i]);
        i += 1;
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn asarray(a: Vec<f32>) -> (result: Vec<f32>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): call copy_vec to build and return a new Vec<f32> */
    copy_vec(a)
}
// </vc-code>

}
fn main() {}