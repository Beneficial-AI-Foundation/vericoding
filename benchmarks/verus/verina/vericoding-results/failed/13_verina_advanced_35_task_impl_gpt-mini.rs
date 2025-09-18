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
/* helper modified by LLM (iteration 5): sum of counts of two distinct values <= length */
proof fn counts_pair_le_len(nums: Seq<i32>, x: i32, y: i32)
    requires
        x != y,
    decreases nums.len()
    ensures
        count_occurrences(nums, x) + count_occurrences(nums, y) <= nums.len(),
{
    if nums.len() == 0 {
    } else {
        let first = nums[0];
        let rest = nums.subrange(1, nums.len() as int);
        counts_pair_le_len(rest, x, y);
        if first == x {
            assert(count_occurrences(nums, x) == count_occurrences(rest, x) + 1);
            assert(count_occurrences(nums, y) == count_occurrences(rest, y));
            assert(count_occurrences(rest, x) + count_occurrences(rest, y) <= rest.len());
            assert(count_occurrences(rest, x) + count_occurrences(rest, y) + 1 <= rest.len() + 1);
            assert(count_occurrences(nums, x) + count_occurrences(nums, y) <= nums.len());
        } else if first == y {
            assert(count_occurrences(nums, x) == count_occurrences(rest, x));
            assert(count_occurrences(nums, y) == count_occurrences(rest, y) + 1);
            assert(count_occurrences(rest, x) + count_occurrences(rest, y) <= rest.len());
            assert(count_occurrences(rest, x) + count_occurrences(rest, y) + 1 <= rest.len() + 1);
            assert(count_occurrences(nums, x) + count_occurrences(nums, y) <= nums.len());
        } else {
            assert(count_occurrences(nums, x) == count_occurrences(rest, x));
            assert(count_occurrences(nums, y) == count_occurrences(rest, y));
            assert(count_occurrences(rest, x) + count_occurrences(rest, y) <= rest.len());
            assert(count_occurrences(nums, x) + count_occurrences(nums, y) <= nums.len());
        }
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
{
    /* code modified by LLM (iteration 5): choose majority element and prove others have <= n/2 by contradiction using counts_pair_le_len */
    let result = choose|v: i32| count_occurrences(nums, v) > nums.len() / 2;
    proof {
        assert(count_occurrences(nums, result) > nums.len() / 2);
        assert(forall|x: i32|
            x != result ==>
                {
                    counts_pair_le_len(nums, x, result);
                    if count_occurrences(nums, x) > nums.len() / 2 {
                        assert(count_occurrences(nums, x) + count_occurrences(nums, result) > nums.len());
                        counts_pair_le_len(nums, x, result);
                        assert(false);
                    }
                    true
                }
        );
    }
    result
}

// </vc-code>

}
fn main() {}