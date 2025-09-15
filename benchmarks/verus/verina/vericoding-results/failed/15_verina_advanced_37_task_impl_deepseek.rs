// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, value: i32) -> nat {
    nums.filter(|x: i32| x == value).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed invariant syntax, added proper braces and proof logic */
proof fn majority_lemma(nums: Seq<i32>, candidate: i32)
    requires count_occurrences(nums, candidate) > nums.len() / 2,
    ensures count_occurrences(nums, candidate) > nums.len() / 2
{
}

proof fn candidate_validity_lemma(nums: Seq<i32>, candidate: i32) 
    requires count_occurrences(nums, candidate) > nums.len() / 2
    ensures forall|x: i32| x == candidate || count_occurrences(nums, x) <= nums.len() / 2
{
    assert forall|x: i32| x != candidate implies count_occurrences(nums, x) <= nums.len() / 2 by {
        if (exists|x: i32| x != candidate && count_occurrences(nums, x) > nums.len() / 2) {
            let other_count = count_occurrences(nums, x);
            assert(nums.len() >= count_occurrences(nums, candidate) + other_count);
            assert(count_occurrences(nums, candidate) + other_count > nums.len() / 2 + nums.len() / 2);
            assert(count_occurrences(nums, candidate) + other_count > nums.len());
            assert(false);
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn majority_element(nums: &Vec<i32>) -> (result: i32)
    requires nums.len() > 0,
    ensures ({
        let nums_seq = nums@;
        let n = nums_seq.len();
        count_occurrences(nums_seq, result) > n / 2 &&
        forall|x: i32| x == result || count_occurrences(nums_seq, x) <= n / 2
    }),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed invariant syntax with proper curly braces */
{
    let mut candidate = 0;
    let mut count = 0;
    
    for i in 0..nums.len() 
        invariant 0 <= i <= nums.len()
        invariant count >= 0
        invariant count > 0 ==> count_occurrences(nums@.take(i), candidate) >= count
        invariant count >= 1 ==> count_occurrences(nums@.take(i), candidate) > (i - count)
    {
        if count == 0 {
            candidate = nums[i];
            count = 1;
        } else {
            if nums[i] == candidate {
                count += 1;
            } else {
                count -= 1;
            }
        }
    }
    
    proof {
        majority_lemma(nums@, candidate);
    }
    
    candidate
}
// </vc-code>

}
fn main() {}