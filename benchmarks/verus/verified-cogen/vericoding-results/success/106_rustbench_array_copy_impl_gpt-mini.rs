// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): convert usize to int for specs */
spec fn usize_to_int(u: usize) -> int { u as int }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_copy(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): copy elements with invariants using int indices */
    let mut res: Vec::<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j && j < usize_to_int(i) ==> res[j] == a[j],
        decreases a.len() - i
    {
        res.push(a[i]);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}