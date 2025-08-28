use vstd::prelude::*;

verus! {

//https://leetcode.com/problems/remove-element/

// <vc-helpers>
// No updates needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn removeElement(nums: &mut Vec<i32>, val: i32) -> (i: usize)
    ensures forall|k: int| 0 < k < i && k < nums.len() ==> nums[k] != val,
// </vc-spec>
// </vc-spec>

// <vc-code>
fn removeElement(nums: &mut Vec<i32>, val: i32) -> (i: usize)
    ensures forall|k: int| 0 <= k < i && k < nums.len() ==> nums[k] != val,
{
    let mut i: usize = 0;
    let mut j: usize = 0;
    let len = nums.len();
    
    while j < len
        invariant
            i <= j,
            j <= len,
            forall|k: int| 0 <= k < i && k < nums.len() ==> nums@[k] != val,
    {
        if nums@[j] != val {
            if i != j {
                let tmp = nums@[i];
                nums.set(i, nums@[j]);
                nums.set(j, tmp);
            }
            i = i + 1;
        }
        j = j + 1;
    }
    i
}
// </vc-code>

fn main() {}

}