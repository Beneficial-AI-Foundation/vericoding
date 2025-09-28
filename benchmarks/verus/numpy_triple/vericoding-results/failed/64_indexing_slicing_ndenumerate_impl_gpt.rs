// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemma to relate usize indices to int range with disambiguating parentheses */
proof fn lemma_index_range(len: usize, i: usize)
    requires
        i < len,
    ensures
        0 <= (i as int),
        (i as int) < (len as int),
{
    assert(0 <= (i as int));
    assert((i as int) < (len as int));
}

// </vc-helpers>

// <vc-spec>
fn ndenumerate(arr: Vec<f32>) -> (result: Vec<(usize, f32)>)
    ensures 
        result.len() == arr.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i as int].0 == i && result[i as int].1 == arr[i as int]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement enumeration with loop invariants ensuring correctness of indices and values */
    let mut result: Vec<(usize, f32)> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            result.len() == i,
            i <= arr.len(),
            forall|j: int| 0 <= j < (i as int) ==> result@[j].0 == j as usize && result@[j].1 == arr@[j],
        decreases arr.len() - i
    {
        let v = arr[i];
        result.push((i, v));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}