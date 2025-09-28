use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let old_len = nums.len();
    let original = nums@;
    let mut i = 0;
    for j in 0..old_len
        invariant
            0 <= i as int <= j as int <= old_len,
            nums.len() == old_len,
            forall|k: int| 0 <= k < i as int ==> nums[k] != val,
            nums@.subrange(0, i as int).to_multiset() == original@.subrange(0, j as int).to_multiset().remove(val),
    {
        if nums[j] != val {
            nums[i] = nums[j];
            i += 1;
        }
    }
    i
}
// </vc-code>

fn main() {
}

}