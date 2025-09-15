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
fn boyer_moore(nums: Seq<i32>) -> (candidate: i32)
    requires nums.len() > 0
    requires exists|x: i32| count_occurrences(nums, x) > nums.len() / 2
    ensures
       count_occurrences(nums, candidate) > nums.len() / 2,
       forall|x: i32| x != candidate ==> count_occurrences(nums, x) <= nums.len() / 2
{
    let mut candidate: i32 = nums[0 as int];
    let mut count: i32 = 1;
    let mut i: usize = 1;
    while i < nums.len()
        invariant i <= nums.len(), count >= 0, i >= 1
    {
        if nums[i as int] == candidate {
           count += 1;
        } else {
           count -= 1;
           if count == 0 {
               if i + 1 < nums.len() {
                   candidate = nums[(i + 1) as int];
                   i += 1;
                   count = 1;
               }
           }
        }
        i += 1;
    }
    proof {
        assert(count_occurrences(nums, candidate) > nums.len() / 2);
    }
    candidate
}
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
    boyer_moore(nums)
}
// </vc-code>

}
fn main() {}