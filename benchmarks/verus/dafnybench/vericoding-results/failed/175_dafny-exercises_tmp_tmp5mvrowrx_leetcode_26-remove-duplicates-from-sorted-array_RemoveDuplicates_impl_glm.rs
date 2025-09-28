use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_duplicates(nums: &mut Vec<i32>) -> (num_length: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < old(nums).len() ==> old(nums)[i] <= old(nums)[j],
    ensures
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums[i] != nums[j],
        forall|i: int| 0 <= i < num_length ==> old(nums)@.contains(nums[i]),
        forall|i: int| 0 <= i < old(nums).len() ==> nums@.subrange(0, num_length as int).contains(old(nums)[i]),
// </vc-spec>
// <vc-code>
{
    let n = nums.len();
    if n == 0 {
        return 0;
    }
    let mut insert_index = 0;
    let mut i = 0;
    while i < n
        invariant
            0 <= insert_index <= i <= n,
            forall|a: int, b: int| 0 <= a < b < (insert_index as int) ==> nums[a] != nums[b],
            forall|k: int| 0 <= k < (insert_index as int) ==> old(nums)@.contains(nums[k]),
            forall|k: int| 0 <= k < (i as int) ==> nums@.subrange(0, (insert_index as int)).contains(old(nums)[k]),
    {
        if i == 0 {
            let value = nums[0];
            nums.set(insert_index, value);
            insert_index = insert_index + 1;
        } else if nums[i] != nums[i-1] {
            let value = nums[i];
            nums.set(insert_index, value);
            insert_index = insert_index + 1;
        }
        i = i + 1;
    }
    insert_index
}
// </vc-code>

fn main() {
}

}