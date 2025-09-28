use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed.
// </vc-helpers>

// <vc-spec>
fn remove_element(nums: &mut Vec<i32>, val: i32) -> (newLength: usize)
    ensures 
        0 <= newLength <= nums.len(),
        forall|i: int| 0 <= i < newLength ==> nums[i] != val,
        nums@.subrange(0, newLength as int).to_multiset() == 
            old(nums)@.to_multiset().remove(val),
// </vc-spec>
// <vc-code>
{
    let old_nums: Seq<i32> = nums@;
    let n: int = nums.len() as int;
    let mut i: int = 0;
    let mut k: int = 0;
    while i < n
        invariant i <= n;
        invariant k <= i;
        invariant forall |idx: int| 0 <= idx && idx < k ==> nums@[idx] != val;
        invariant nums@.subrange(0, k).to_multiset() == old_nums.subrange(0, i).to_multiset().remove(val);
        invariant forall |j: int| i <= j && j < n ==> nums@[j] == old_nums@[j];
        decreases (n - i);
    {
        let cur: i32 = nums[i as usize];
        if cur != val {
            nums[k as usize] = cur;
            proof {
                // the element at i in the current nums equals the old one
                assert(nums@[i] == old_nums@[i]);
                // after assignment, nums@[k] equals cur
                assert(nums@[k] == cur);
                // preserve previous multiset relation for prefix of length k
                assert(nums@.subrange(0, k).to_multiset() == old_nums.subrange(0, i).to_multiset().remove(val));
                // extending the prefix by cur updates the multiset accordingly
                assert(nums@.subrange(0, k + 1).to_multiset() == nums@.subrange(0, k).to_multiset().insert(cur));
                // cur matches the old element at position i
                assert(cur == old_nums@[i]);
                // extending old prefix by cur
                assert(old_nums.subrange(0, i + 1).to_multiset() == old_nums.subrange(0, i).to_multiset().insert(cur));
                // removing val commutes with the insertion of cur (since cur != val here)
                assert(old_nums.subrange(0, i + 1).to_multiset().remove(val) ==
                       old_nums.subrange(0, i).to_multiset().remove(val).insert(cur));
                // conclude the multiset relation for the extended k
                assert(nums@.subrange(0, k + 1).to_multiset() ==
                       old_nums.subrange(0, i + 1).to_multiset().remove(val));
            }
            k = k + 1;
        }
        i = i + 1;
    }
    k as usize
}
// </vc-code>

fn main() {
}

}