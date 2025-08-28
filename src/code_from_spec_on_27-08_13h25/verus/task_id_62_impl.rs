use vstd::prelude::*;


verus! {

// <vc-helpers>
proof fn lemma_vec_index_le_len<T>(v: &Vec<T>, i: int)
    requires
        0 <= i,
        i < v.len(),
    ensures
        0 <= i < v.len(),
{
}
// </vc-helpers>

// <vc-spec>
fn smallest_num(nums: &Vec<i32>) -> (min: i32)
    // pre-conditions-start
    requires
        nums.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| 0 <= i < nums.len() ==> min <= nums[i],
        exists|i: int| 0 <= i < nums.len() && min == nums[i],
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn smallest_num(nums: &Vec<i32>) -> (min: i32)
    requires
        nums.len() > 0,
    ensures
        forall|i: int| 0 <= i < nums.len() ==> min <= nums@[i],
        exists|i: int| 0 <= i < nums.len() && min == nums@[i],
{
    let mut min_val = nums@[0];
    let mut index = 1;

    while index < nums.len()
        invariant
            0 <= index <= nums.len(),
            forall|k: int| 0 <= k < index ==> min_val <= nums@[k],
            exists|k: int| 0 <= k < index && min_val == nums@[k],
    {
        if nums@[index] < min_val {
            min_val = nums@[index];
        }
        index = index + 1;
    }

    min_val
}
// </vc-code>

} // verus!

fn main() {}