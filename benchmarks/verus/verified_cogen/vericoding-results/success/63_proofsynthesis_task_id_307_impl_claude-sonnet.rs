// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)

    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to fix compilation error */
    let mut copied = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            copied@.len() == i,
            forall|j: int| (0 <= j < i) ==> arr[j] == copied[j],
        decreases arr.len() - i
    {
        copied.push(arr[i]);
        i = i + 1;
    }
    copied
}
// </vc-code>

}
fn main() {}