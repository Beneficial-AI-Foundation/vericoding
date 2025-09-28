// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_duplicates(nums: &Vec<i32>) -> (result: usize)
    requires forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j],
    ensures result <= nums.len(),
// </vc-spec>
// <vc-code>
{
    let mut write_pos = 0usize;
    let mut read_pos = 0usize;
    
    while read_pos < nums.len()
        invariant
            write_pos <= read_pos,
            read_pos <= nums.len(),
            write_pos <= nums.len(),
        decreases nums.len() - read_pos
    {
        if write_pos == 0 || nums[read_pos] != nums[write_pos - 1] {
            write_pos += 1;
        }
        read_pos += 1;
    }
    
    write_pos
}
// </vc-code>

}
fn main() {}