// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn distinct(nums: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax of forall proof block from 'where' to 'requires/ensures' */
proof fn lemma_distinct_subrange_extend(nums: Seq<int>, i: int)
    requires
        0 <= i < nums.len(),
        distinct(nums.subrange(0, i)),
        forall|k: int| 0 <= k < i ==> nums[k] != nums[i],
    ensures
        distinct(nums.subrange(0, i + 1)),
{
    forall|j: int, k: int|
        requires 0 <= j < k < i + 1
        ensures nums[j] != nums[k]
    {
        if k < i {
            assert(distinct(nums.subrange(0, i)));
        } else { // k == i
            assert(nums[j] != nums[i]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn contains_duplicate(nums: Seq<int>) -> (result: bool)
    requires
        1 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= -1000000000 && nums[i] <= 1000000000,
    ensures
        result <==> distinct(nums),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no logical changes, previous logic was sound, only helper was fixed */
{
    let mut i: int = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            distinct(nums.subrange(0, i)),
        decreases nums.len() - i
    {
        let mut j: int = 0;
        while j < i
            invariant
                0 <= j <= i,
                forall|k: int| 0 <= k < j ==> nums[k] != nums[i],
            decreases i - j
        {
            if nums[j] == nums[i] {
                return false;
            }
            j = j + 1;
        }

        assert(forall|k: int| 0 <= k < i ==> nums[k] != nums[i]);
        lemma_distinct_subrange_extend(nums, i);
        
        i = i + 1;
    }

    return true;
}
// </vc-code>

}
fn main() {}