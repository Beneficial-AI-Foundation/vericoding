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
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing duplicate lemma keyword */
proof fn lemma_count_occurrences_subrange(nums: Seq<i32>, x: i32, start: int, end: int)
    requires
        0 <= start <= end <= nums.len(),
    ensures
        count_occurrences(nums.subrange(start, end), x) <= count_occurrences(nums, x),
    decreases end - start
{
    if start == end {
        return;
    }
    if start + 1 == end {
        return;
    }
    let mid = start + (end - start) / 2;
    lemma_count_occurrences_subrange(nums, x, start, mid);
    lemma_count_occurrences_subrange(nums, x, mid, end);
}

proof fn lemma_majority_unique(nums: Seq<i32>, x: i32, y: i32)
    requires
        count_occurrences(nums, x) > nums.len() / 2,
        count_occurrences(nums, y) > nums.len() / 2,
    ensures
        x == y,
{
    if x != y {
        assert(count_occurrences(nums, x) + count_occurrences(nums, y) > nums.len());
        lemma_count_sum_bound(nums, x, y);
        assert(false);
    }
}

proof fn lemma_count_sum_bound(nums: Seq<i32>, x: i32, y: i32)
    requires
        x != y,
    ensures
        count_occurrences(nums, x) + count_occurrences(nums, y) <= nums.len(),
    decreases nums.len()
{
    if nums.len() == 0 {
        return;
    }
    let first = nums[0];
    let rest = nums.subrange(1, nums.len() as int);
    lemma_count_sum_bound(rest, x, y);
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
    /* code modified by LLM (iteration 5): fixed type error by using usize for loop counter */
    let mut candidate = nums@[0];
    let mut count = 1;
    let mut i: usize = 1;
    
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            count >= 0,
            exists|x: i32| count_occurrences(nums, x) > nums.len() / 2,
        decreases nums.len() - i
    {
        if nums@[i as int] == candidate {
            count = count + 1;
        } else {
            count = count - 1;
            if count == 0 {
                candidate = nums@[i as int];
                count = 1;
            }
        }
        i = i + 1;
    }
    
    proof {
        assert(exists|x: i32| count_occurrences(nums, x) > nums.len() / 2);
        let witness_x = choose|x: i32| count_occurrences(nums, x) > nums.len() / 2;
        
        if count_occurrences(nums, candidate) <= nums.len() / 2 {
            lemma_majority_unique(nums, witness_x, candidate);
            assert(false);
        }
        
        assert(count_occurrences(nums, candidate) > nums.len() / 2);
        
        assert(forall|x: i32| x != candidate ==> {
            if count_occurrences(nums, x) > nums.len() / 2 {
                lemma_majority_unique(nums, candidate, x);
                false
            } else {
                true
            }
        });
    }
    
    candidate
}
// </vc-code>

}
fn main() {}