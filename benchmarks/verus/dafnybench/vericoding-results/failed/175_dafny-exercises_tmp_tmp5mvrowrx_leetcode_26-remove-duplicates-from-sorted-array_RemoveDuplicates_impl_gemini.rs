// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_duplicates(nums: &mut Vec<i32>) -> (num_length: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < old(nums).len() ==> old(nums)[i] <= old(nums)[j],
    ensures
        nums.len() == old(nums).len(),
        0 <= num_length <= nums.len(),
        forall|i: int, j: int| 0 <= i < j < num_length ==> nums[i] != nums[j],
        forall|i: int| 0 <= i < num_length ==> old(nums)@.contains(nums[i]),
        forall|i: int| 0 <= i < old(nums).len() ==> nums@.subrange(0, num_length as int).contains(old(nums)[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): replaced set equivalence with directional invariants and added proof for duplicate case */
{
    if nums.len() == 0 {
        return 0;
    }

    let ghost old_nums = nums@;

    let mut k: usize = 1;
    let mut i: usize = 1;

    while i < nums.len()
        invariant
            nums.len() == old_nums.len(),
            1 <= k <= i,
            i <= nums.len(),
            forall|m: int, n: int| 0 <= m < n < old_nums.len() ==> old_nums[m] <= old_nums[n],
            forall|m: int, n: int| 0 <= m < n < k ==> nums[m] < nums[n],
            forall|j: int| i <= j < nums.len() ==> nums[j] == old_nums[j],
            forall|j: int| 0 <= j < i ==> nums@.subrange(0, k as int).contains(old_nums[j]),
            forall|j: int| 0 <= j < k ==> old_nums.subrange(0, i as int).contains(nums[j]),
        decreases nums.len() - i
    {
        let val = nums[i];
        let last_unique = nums[k - 1];

        if val > last_unique {
            nums[k] = val;
            k = k + 1;
        } else {
            proof {
                assert(val <= last_unique);
                assert(old_nums.subrange(0, i as int).contains(last_unique));
                let p = vstd::seq::find_first_match(old_nums.subrange(0, i as int), |item: i32| item == last_unique).get_Some_0();
                assert(p < i);
                assert(old_nums[p as int] == last_unique);
                assert(old_nums[p as int] <= old_nums[i]); 
                assert(old_nums[i] <= old_nums[p as int]); 
                assert(val == old_nums[p as int]);
                assert(nums@.subrange(0, k as int).contains(old_nums[p as int]));
                assert(nums@.subrange(0, k as int).contains(val));
            }
        }

        i = i + 1;
    }

    k
}
// </vc-code>

}
fn main() {}