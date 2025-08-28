use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)
    // post-conditions-start
    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut copied = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            copied@.len() == i,
            forall|j: int| (0 <= j < i) ==> arr[j] == copied[j],
        decreases arr.len() - i,
    {
        copied.push(arr[i]);
        i += 1;
    }
    assert(i == arr.len());
    assert(copied@.len() == i);
    copied
}
// </vc-code>

} // verus!

fn main() {}