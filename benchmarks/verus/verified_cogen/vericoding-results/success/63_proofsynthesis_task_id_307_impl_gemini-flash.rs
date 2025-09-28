// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No helpers required. */
// </vc-helpers>

// <vc-spec>
fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)

    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Added `decreases arr.len() - i` to loop */
{
    let mut copied = Vec::new();
    let mut i: usize = 0;

    while i < arr.len()
        invariant 
            0 <= i as int,
            i as int <= arr.len() as int,
            copied@.len() == i as nat,
            // All elements copied so far are identical to original
            forall|j: int| (0 <= j < i as int) ==> arr@.index(j) == copied@.index(j),
        decreases arr.len() - i
    {
        // We can push since `copied` has `i` elements and will have `i+1`
        // The `push` method increases capacity if needed.
        // It is `ghost_mut` because it affects the ghost view of `copied`.
        // We need to keep `arr` as `&Vec` so it's not moved.
        copied.push(arr[i]);
        i = i + 1;
    }
    copied
}
// </vc-code>

}
fn main() {}