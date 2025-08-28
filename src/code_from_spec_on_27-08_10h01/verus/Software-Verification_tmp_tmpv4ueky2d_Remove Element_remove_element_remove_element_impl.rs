use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn remove_element(nums: &mut Vec<i32>, val: i32) -> (i: usize)
    requires 
        old(nums).len() <= 100,
        forall|j: int| 0 <= j < old(nums).len() ==> #[trigger] old(nums)[j] >= 0 && old(nums)[j] <= 50,
        0 <= val <= 100,
    ensures
        forall|j: int| 0 < j < i < nums.len() ==> #[trigger] nums[j] != val,
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut write_idx = 0;
    let mut read_idx = 0;
    
    while read_idx < nums.len()
        invariant
            write_idx <= read_idx,
            read_idx <= nums.len(),
            write_idx <= nums.len(),
            forall|j: int| 0 <= j < write_idx ==> nums[j as int] != val,
            forall|j: int| write_idx <= j < nums.len() ==> nums[j as int] == old(nums)[j as int],
    {
        if nums[read_idx] != val {
            nums.set(write_idx, nums[read_idx]);
            write_idx += 1;
        }
        read_idx += 1;
    }
    
    write_idx
}
// </vc-code>

fn main() {
}

}