// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bmat(top_left: Vec<f32>, top_right: Vec<f32>, bottom_left: Vec<f32>, bottom_right: Vec<f32>) -> (result: Vec<f32>)
    requires 
        top_left.len() == top_right.len(),
        top_left.len() == bottom_left.len(),
        top_left.len() == bottom_right.len(),
    ensures
        result.len() == 4 * top_left.len(),
        forall|i: int| 0 <= i < top_left.len() ==> result[i] == top_left[i],
        forall|i: int| 0 <= i < top_right.len() ==> result[i + top_left.len()] == top_right[i],
        forall|i: int| 0 <= i < bottom_left.len() ==> result[i + 2 * top_left.len()] == bottom_left[i],
        forall|i: int| 0 <= i < bottom_right.len() ==> result[i + 3 * top_left.len()] == bottom_right[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): replaced extend with manual push loops and invariants */
    let mut result = Vec::new();
    let mut i = 0;
    while i < top_left.len()
        invariant
            0 <= i <= top_left.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == top_left@[j],
        decreases top_left.len() - i
    {
        result.push(top_left[i]);
        i += 1;
    }
    i = 0;
    while i < top_right.len()
        invariant
            0 <= i <= top_right.len(),
            result.len() == top_left.len() + i,
            forall|j: int| 0 <= j < top_left.len() ==> result@[j] == top_left@[j],
            forall|j: int| top_left.len() <= j < top_left.len() + i ==> result@[j] == top_right@[j - top_left.len()],
        decreases top_right.len() - i
    {
        result.push(top_right[i]);
        i += 1;
    }
    i = 0;
    while i < bottom_left.len()
        invariant
            0 <= i <= bottom_left.len(),
            result.len() == 2 * top_left.len() + i,
            forall|j: int| 0 <= j < top_left.len() ==> result@[j] == top_left@[j],
            forall|j: int| top_left.len() <= j < 2 * top_left.len() ==> result@[j] == top_right@[j - top_left.len()],
            forall|j: int| 2 * top_left.len() <= j < 2 * top_left.len() + i ==> result@[j] == bottom_left@[j - 2 * top_left.len()],
        decreases bottom_left.len() - i
    {
        result.push(bottom_left[i]);
        i += 1;
    }
    i = 0;
    while i < bottom_right.len()
        invariant
            0 <= i <= bottom_right.len(),
            result.len() == 3 * top_left.len() + i,
            forall|j: int| 0 <= j < top_left.len() ==> result@[j] == top_left@[j],
            forall|j: int| top_left.len() <= j < 2 * top_left.len() ==> result@[j] == top_right@[j - top_left.len()],
            forall|j: int| 2 * top_left.len() <= j < 3 * top_left.len() ==> result@[j] == bottom_left@[j - 2 * top_left.len()],
            forall|j: int| 3 * top_left.len() <= j < 3 * top_left.len() + i ==> result@[j] == bottom_right@[j - 3 * top_left.len()],
        decreases bottom_right.len() - i
    {
        result.push(bottom_right[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}