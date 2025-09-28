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
    if nums.len() == 0 {
        return 0;
    }
    let mut write_pos: usize = 1;
    let mut i: usize = 1;
    while i < nums.len()
        decreases (nums.len() as int - i as int)
        invariant
            write_pos <= i + 1,
            forall |k: int| 0 <= k < ((write_pos - 1) as int) ==> forall |l: int| k < l < ((write_pos - 1) as int) ==> nums@[k] != nums@[l],
            forall |k: int| 0 <= k < write_pos ==> old(nums)@.contains(nums@[k]),
            0 <= i <= nums.len(),
    {
        if nums[i] != nums[i - 1] {
            proof {
                assert(nums@[(i as int)] >= nums@[((i - 1) as int)]);
            }
            nums[write_pos] = nums[i];
            write_pos = write_pos + 1;
            proof {
                assert(forall |k: int| 0 <= k < ((write_pos - 1) as int) ==> nums@[k] != nums@[((write_pos - 1) as int)]);
                assert(old(nums)@.contains(nums@[((write_pos - 1) as int)]));
            }
        }
        i = i + 1;
    }
    assert(forall |k: int, l: int| 0 <= k < l < ((write_pos as int)) ==> nums@[k] != nums@[l]);
    assert(forall |k: int| 0 <= k < ((write_pos as int)) ==> old(nums)@.contains(nums@[k]));
    assert(forall |i: int| 0 <= i < old(nums).len() ==> nums@.subrange(0, write_pos as int).contains(old(nums)@[i]));

    write_pos
}
// </vc-code>

fn main() {
}

}