use vstd::prelude::*;

verus! {

// <vc-helpers>
use vstd::multiset::Multiset;
fn multiset_remove_one<V: core::cmp::PartialEq + core::hash::Hash + core::cmp::Eq>(ms: Multiset<V>, val: V) -> Multiset<V> {
    ms.remove(val)
}

/// A custom swap function that can be verified by Verus.
/// This replaces the standard library `swap` function which is not yet supported.
fn vec_swap<T>(vec: &mut Vec<T>, i: usize, j: usize)
    requires
        0 <= i < vec.len(),
        0 <= j < vec.len(),
    ensures
        vec.len() == old(vec).len(),
        ({
            let old_vec = old(vec);
            let mut new_vec = old_vec.to_seq();
            let temp = new_vec.index(i);
            new_vec = new_vec.update(i, new_vec.index(j));
            new_vec = new_vec.update(j, temp);
            vec@ == new_vec
        })
{
    // The following swaps elements at indices i and j
    // Since direct `core::slice::impl::swap` is not supported,
    // we manually implement the swap logic.
    let val_i = vec[i];
    let val_j = vec[j];
    vec.set(i, val_j);
    vec.set(j, val_i);
}
// </vc-helpers>

// <vc-spec>
fn remove_element(nums: &mut Vec<i32>, val: i32) -> (newLength: usize)
    ensures 
        0 <= newLength <= nums.len(),
        forall|i: int| 0 <= i < newLength ==> nums[i] != val,
        nums@.subrange(0, newLength as int).to_multiset() == 
            old(nums)@.to_multiset().remove(val),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut j: usize = 0;
    let original_len = nums.len();
    let original_nums = nums@;

    while j < original_len
        invariant
            0 <= i as int && i as int <= j as int && j as int <= original_len as int,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] != val,
            nums@.subrange(0, i as int).to_multiset() =~~= original_nums.subrange(0, j as int).to_multiset().remove(val), // Use =~~= for multiset equality
            nums@.subrange(j as int, original_len as int) == original_nums.subrange(j as int, original_len as int),
            nums.len() == original_len, // Add this invariant to satisfy the postcondition of `vec_swap`
    {
        if nums[j] != val {
            vec_swap(nums, i, j); // Fix: Remove `&mut` as `nums` is already a mutable reference
            i = i + 1;
        }
        j = j + 1;
    }

    nums.truncate(i); 

    let newLength = i;
    newLength
}
// </vc-code>

fn main() {
}

}