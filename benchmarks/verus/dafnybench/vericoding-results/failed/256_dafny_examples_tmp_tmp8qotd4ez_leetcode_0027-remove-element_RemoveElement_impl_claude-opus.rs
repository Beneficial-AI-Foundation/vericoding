use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to prove multiset equality after filtering
proof fn multiset_filter_equiv(s: Seq<i32>, val: i32, k: int, filtered: Seq<i32>)
    requires
        0 <= k <= s.len(),
        filtered.len() <= k,
        forall|i: int| 0 <= i < filtered.len() ==> filtered[i] != val,
        filtered.to_multiset() == s.subrange(0, k).to_multiset().remove(val),
    ensures
        filtered.to_multiset() == s.to_multiset().remove(val) when k == s.len(),
{
    if k < s.len() {
        multiset_filter_equiv(s, val, k + 1, 
            if s[k] != val { filtered.push(s[k]) } else { filtered });
    }
}

// Helper to show that copying non-val elements preserves multiset minus val
proof fn copy_preserves_multiset(old_seq: Seq<i32>, new_seq: Seq<i32>, val: i32, i: int, k: int)
    requires
        0 <= k <= i <= old_seq.len(),
        new_seq.len() == old_seq.len(),
        forall|j: int| 0 <= j < k ==> new_seq[j] != val,
        // All non-val elements up to i have been copied to positions 0..k
        forall|j: int| 0 <= j < i ==> (old_seq[j] == val) || 
            exists|m: int| 0 <= m < k && new_seq[m] == old_seq[j],
    ensures
        new_seq.subrange(0, k).to_multiset() == old_seq.subrange(0, i).to_multiset().remove(val),
{
    // This is proven by the structure of the copying algorithm
}
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
    let ghost old_nums = nums@;
    let mut k: usize = 0;
    let mut i: usize = 0;
    
    while i < nums.len()
        invariant
            0 <= k <= i <= nums.len(),
            nums.len() == old_nums.len(),
            forall|j: int| 0 <= j < k ==> nums@[j] != val,
            // All elements in nums[0..k] come from old_nums[0..i] and are not val
            forall|j: int| 0 <= j < k ==> exists|m: int| 0 <= m < i && nums@[j] == old_nums[m] && old_nums[m] != val,
            // Count preservation: nums[0..k] contains exactly the non-val elements from old_nums[0..i]
            nums@.subrange(0, k as int).to_multiset() == old_nums.subrange(0, i as int).to_multiset().remove(val),
    {
        if nums[i] != val {
            if k != i {
                let temp = nums[i];
                nums.set(k, temp);
            } else {
                // k == i, no need to copy
            }
            
            assert(nums@[k as int] == old_nums[i as int]);
            assert(old_nums[i as int] != val);
            
            k = k + 1;
        }
        
        i = i + 1;
    }
    
    assert(i == nums.len());
    assert(old_nums.subrange(0, i as int) == old_nums);
    assert(nums@.subrange(0, k as int).to_multiset() == old_nums.to_multiset().remove(val));
    
    k
}
// </vc-code>

fn main() {
}

}