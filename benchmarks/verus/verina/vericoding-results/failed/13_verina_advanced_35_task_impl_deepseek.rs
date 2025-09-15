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
/* helper modified by LLM (iteration 5): Fix type errors and improve lemma */
proof fn lemma_count_occurrences_subrange(nums: Seq<i32>, x: i32, start: int, end: int)
    requires 
        0 <= start <= end <= nums.len(),
    ensures 
        count_occurrences(nums.subrange(start, end), x) == count_occurrences(nums, x) - count_occurrences(nums.subrange(0, start), x) - count_occurrences(nums.subrange(end, nums.len()), x)
{
    // Base case implementation
    if start == end {
        assert(nums.subrange(start, end).len() == 0);
        assert(count_occurrences(nums.subrange(start, end), x) == 0);
    }
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
/* code modified by LLM (iteration 5): Fix type errors and simplify implementation */
{
    let n: nat = nums.len();
    let mut candidate: i32 = 0;
    let mut count: int = 0;
    
    let mut i: int = 0;
    while i < n as int
        invariant 
            0 <= i <= n as int,
            count >= 0,
            count <= i,
            (count > 0 ==> count_occurrences(nums.subrange(0, i), candidate) > (i - count) / 2),
            (count == 0 ==> forall|j: int| 0 <= j < i ==> count_occurrences(nums.subrange(0, i), nums@[j as nat]) <= i / 2)
    {
        let current = nums@[i as nat];
        if count == 0 {
            candidate = current;
            count = 1;
        } else if candidate == current {
            count = count + 1;
        } else {
            count = count - 1;
        }
        i = i + 1;
    }
    
    candidate
}
// </vc-code>

}
fn main() {}