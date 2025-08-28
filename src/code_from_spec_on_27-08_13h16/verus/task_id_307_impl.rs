use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this fix
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
    let mut copied: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            copied@.len() == i,
            forall|j: int| 0 <= j < i ==> copied@[j] == arr@[j],
        decreases arr.len() - i
    {
        copied.push(arr[i]);
        i = i + 1;
    }
    
    copied
}
// </vc-code>

} // verus!

fn main() {}