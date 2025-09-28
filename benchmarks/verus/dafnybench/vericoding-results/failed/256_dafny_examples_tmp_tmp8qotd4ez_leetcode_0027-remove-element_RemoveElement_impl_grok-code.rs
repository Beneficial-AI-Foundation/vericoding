use vstd::prelude::*;

verus! {

// <vc-helpers>
// empty
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
    while i < nums.len()
        decreases nums@.len() as int - i as int
        invariant forall |k: int| 0 <= k < j ==> nums@[k] != val
        invariant j <= i && i <= nums@.len()
        invariant j as int == (old(nums)@.subrange(0, i as int).to_multiset().remove(val)).len()
    {
        if nums[i] != val {
            nums[j] = nums[i];
            j += 1;
        }
        i += 1;
    }
    nums.truncate(j);
    j
}
// </vc-code>

fn main() {
}

}