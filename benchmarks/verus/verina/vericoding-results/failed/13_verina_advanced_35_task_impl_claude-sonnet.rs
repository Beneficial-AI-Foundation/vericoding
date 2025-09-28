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
proof fn majority_element_unique(nums: Seq<i32>, x: i32, y: i32)
    requires
        nums.len() > 0,
        count_occurrences(nums, x) > nums.len() / 2,
        count_occurrences(nums, y) > nums.len() / 2,
    ensures x == y
{
    if x != y {
        assert(count_occurrences(nums, x) + count_occurrences(nums, y) > nums.len());
        count_sum_bound(nums, x, y);
        assert(false);
    }
}

proof fn count_sum_bound(nums: Seq<i32>, x: i32, y: i32)
    requires x != y
    ensures count_occurrences(nums, x) + count_occurrences(nums, y) <= nums.len()
    decreases nums.len()
{
    if nums.len() == 0 {
        return;
    }
    let first = nums[0];
    let rest = nums.subrange(1, nums.len() as int);
    count_sum_bound(rest, x, y);
}

/* helper modified by LLM (iteration 5): implement Boyer-Moore voting algorithm to find majority element */
fn boyer_moore_majority(nums: &Vec<i32>) -> (result: i32)
    requires nums@.len() > 0
    ensures true
{
    let mut candidate = nums[0];
    let mut count = 1;
    let mut i = 1;
    
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            count >= 0
    {
        if nums[i] == candidate {
            count += 1;
        } else if count == 0 {
            candidate = nums[i];
            count = 1;
        } else {
            count -= 1;
        }
        i += 1;
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
    /* code modified by LLM (iteration 5): convert seq to vec and use Boyer-Moore algorithm */
    let mut vec_nums = Vec::new();
    let mut i = 0;
    
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            vec_nums@.len() == i,
            forall|j: int| 0 <= j < i ==> vec_nums@[j] == nums[j]
    {
        vec_nums.push(nums[i]);
        i = i + 1;
    }
    
    let candidate = boyer_moore_majority(&vec_nums);
    
    proof {
        let ghost witness = choose|x: i32| count_occurrences(nums, x) > nums.len() / 2;
        majority_element_unique(nums, candidate, witness);
    }
    
    candidate
}
// </vc-code>

}
fn main() {}