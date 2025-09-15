// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, value: i32) -> nat {
    nums.filter(|x: i32| x == value).len()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): count over concatenation equals sum of counts */
proof fn count_concat(nums1: Seq<i32>, nums2: Seq<i32>, v: i32) ensures count_occurrences(nums1 + nums2, v) == count_occurrences(nums1, v) + count_occurrences(nums2, v) decreases nums1.len() + nums2.len() {
    assert((nums1 + nums2).filter(|x: i32| x == v) == nums1.filter(|x: i32| x == v) + nums2.filter(|x: i32| x == v));
    assert(count_occurrences(nums1 + nums2, v) == (nums1 + nums2).filter(|x: i32| x == v).len());
    assert(count_occurrences(nums1, v) == nums1.filter(|x: i32| x == v).len());
    assert(count_occurrences(nums2, v) == nums2.filter(|x: i32| x == v).len());
    assert((nums1 + nums2).filter(|x: i32| x == v).len() == nums1.filter(|x: i32| x == v).len() + nums2.filter(|x: i32| x == v).len());
    assert(count_occurrences(nums1 + nums2, v) == count_occurrences(nums1, v) + count_occurrences(nums2, v));
}

/* helper modified by LLM (iteration 5): counts are non-negative */
proof fn nonneg_count(nums: Seq<i32>, v: i32) ensures count_occurrences(nums, v) >= 0 decreases nums.len() {
    assert(count_occurrences(nums, v) >= 0);
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
/* code modified by LLM (iteration 5): Boyer-Moore majority vote algorithm */
{
    let n = nums.len();
    let mut candidate: i32 = nums[0];
    let mut count: i32 = 0;
    let mut i: usize = 0;
    while i < n
        invariant i <= n,
        decreases n - i
    {
        let v = nums[i];
        if count == 0 {
            candidate = v;
            count = 1;
        } else if v == candidate {
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