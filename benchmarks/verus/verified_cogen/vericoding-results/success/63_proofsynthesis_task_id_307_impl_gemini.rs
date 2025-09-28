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
    let mut copied = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            copied@.len() == i as int,
            forall|j: int| 0 <= j < i ==> copied@[j] == arr@[j],
        decreases arr.len() - i
    {
        let elem = arr[i];
        copied.push(elem);
        i = i + 1;
    }
    copied
}
// </vc-code>

}
fn main() {}