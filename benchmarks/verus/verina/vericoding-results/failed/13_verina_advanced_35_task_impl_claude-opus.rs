// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, x: i32) -> nat 
    decreases nums.len()
{
    if nums.len() == 0 {
        0
    } else {
        let first = nums[0];
        let rest_count = count_occurrences(nums.subrange(1, nums.len() as int), x);
        if first == x {
            rest_count + 1
        } else {
            rest_count
        }
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn majority_element(nums: Seq<i32>) -> (result: i32)
    requires 
        nums.len() > 0,
        exists|x: i32| count_occurrences(nums, x) > nums.len() / 2,
    ensures 
        count_occurrences(nums, result) > nums.len() / 2,
        forall|x: i32| x != result ==> count_occurrences(nums, x) <= nums.len() / 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed int/nat type usage in exec code by using usize indexing */
    let mut candidate = nums[0];
    let mut count = 1i32;
    let mut i = 1usize;
    
    while i < nums.len()
        invariant
            0 < i <= nums.len(),
            count >= 0,
            count > 0 ==> exists|x: i32| candidate == x && count_occurrences(nums.subrange(0, i as int), x) - count_occurrences(nums.subrange(0, i as int), candidate) <= count,
            count > 0 ==> forall|y: i32| y != candidate ==> count_occurrences(nums.subrange(0, i as int), candidate) - count_occurrences(nums.subrange(0, i as int), y) >= count,
            count == 0 ==> forall|x: i32| count_occurrences(nums.subrange(0, i as int), x) <= i / 2,
    {
        if nums[i] == candidate {
            count = count + 1;
        } else if count == 0 {
            candidate = nums[i];
            count = 1;
        } else {
            count = count - 1;
        }
        i = i + 1;
    }
    
    let mut verification_count = 0usize;
    let mut j = 0usize;
    
    while j < nums.len()
        invariant
            0 <= j <= nums.len(),
            verification_count == count_occurrences(nums.subrange(0, j as int), candidate),
    {
        if nums[j] == candidate {
            verification_count = verification_count + 1;
        }
        j = j + 1;
    }
    
    assert(nums.subrange(0, nums.len() as int) =~= nums);
    assert(verification_count == count_occurrences(nums, candidate));
    assert(verification_count > nums.len() / 2);
    
    candidate
}
// </vc-code>

}
fn main() {}