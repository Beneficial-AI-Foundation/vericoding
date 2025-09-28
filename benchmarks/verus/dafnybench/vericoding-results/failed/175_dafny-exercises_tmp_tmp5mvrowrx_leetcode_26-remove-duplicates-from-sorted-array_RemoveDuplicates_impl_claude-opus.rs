use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper function to prove that all elements up to k are unique
proof fn unique_prefix_lemma(nums: &Vec<i32>, k: int)
    requires
        0 <= k <= nums.len(),
        forall|i: int, j: int| 0 <= i < j < k ==> nums[i] != nums[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < k ==> nums[i] != nums[j],
{
}

// Helper to prove containment properties
proof fn contains_lemma(old_nums: Seq<i32>, nums: Seq<i32>, k: int)
    requires
        0 <= k <= nums.len(),
        k <= old_nums.len(),
        forall|i: int| 0 <= i < k ==> old_nums.contains(nums[i]),
    ensures
        forall|i: int| 0 <= i < k ==> old_nums.contains(nums[i]),
{
}

// Helper to establish initial loop invariant
proof fn initial_invariant_lemma(nums: &Vec<i32>)
    requires
        nums.len() > 0,
        forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j],
    ensures
        nums@.subrange(0, 1).contains(#[trigger] nums@[0]),
{
    assert(nums@.subrange(0, 1).len() == 1);
    assert(nums@.subrange(0, 1)[0] == nums@[0]);
}
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
{
    if nums.len() == 0 {
        return 0;
    }

    let mut k: usize = 1;  // Position for next unique element
    let mut i: usize = 1;  // Scanner through the array

    // Establish initial loop invariant
    proof {
        initial_invariant_lemma(nums);
        assert(nums@.subrange(0, 1) =~= seq![nums@[0]]);
        assert(old(nums)@[0] == nums@[0]);
        assert(nums@.subrange(0, 1).contains(old(nums)@[0]));
    }

    while i < nums.len()
        invariant
            1 <= k <= i <= nums.len(),
            nums.len() == old(nums).len(),
            // All elements before k are unique
            forall|a: int, b: int| 0 <= a < b < k ==> nums[a] != nums[b],
            // All elements before k come from original array
            forall|j: int| 0 <= j < k ==> #[trigger] old(nums)@.contains(nums@[j]),
            // All original elements up to i-1 are represented in first k elements
            forall|j: int| 0 <= j < i ==> nums@.subrange(0, k as int).contains(#[trigger] old(nums)@[j]),
            // The array is still sorted up to k
            forall|a: int, b: int| 0 <= a < b < k ==> nums[a] < nums[b],
            // Elements from index k onwards are unchanged from original
            forall|j: int| k <= j < nums.len() ==> nums[j] == old(nums)[j],
            // Current element i hasn't been modified yet
            forall|j: int| i <= j < nums.len() ==> nums[j] == old(nums)[j],
            // Original array is sorted
            forall|a: int, b: int| 0 <= a < b < old(nums).len() ==> old(nums)[a] <= old(nums)[b],
        decreases nums.len() - i,
    {
        let current_val = nums[i];
        let prev_val = nums[(k - 1) as usize];
        
        // Since nums[i] hasn't been modified yet
        assert(nums[i as int] == old(nums)[i as int]);
        assert(current_val == old(nums)[i as int]);
        
        if current_val != prev_val {
            // Found a new unique element
            nums.set(k, current_val);
            
            assert(nums[k as int] == current_val);
            
            // Prove that nums[k] > nums[k-1]
            proof {
                // prev_val is at position k-1, which means it came from some position j < i in old array
                // We need to find this j
                assert(nums[(k - 1) as int] == prev_val);
                // Since all elements before k come from original array and are unique
                // and the original array is sorted, we know that prev_val < current_val
                
                // Since k-1 < k <= i and nums[k-1] comes from old(nums)
                // and all elements up to i-1 are represented in first k elements
                // prev_val appears somewhere in old(nums)[0..i)
                
                // Since original array is sorted and current_val != prev_val
                // and current_val = old(nums)[i]
                // we have prev_val < current_val because of sortedness
                let j_exists = choose|j: int| 0 <= j < i && old(nums)[j] == prev_val;
                assert(0 <= j_exists < i && old(nums)[j_exists] == prev_val);
                assert(old(nums)[j_exists] < old(nums)[i as int]) by {
                    assert(j_exists < i);
                    assert(old(nums)[j_exists] != old(nums)[i as int]);
                    assert(old(nums)[j_exists] <= old(nums)[i as int]);
                }
                assert(prev_val < current_val);
                assert(nums[k as int] > nums[(k - 1) as int]);
            }
            
            k = k + 1;
        }
        
        // Maintain invariant: all elements from old(nums)[0..i] are in nums[0..k]
        proof {
            if current_val != prev_val {
                assert(nums[(k - 1) as int] == current_val);
                assert(nums[(k - 1) as int] == old(nums)[i as int]);
                assert(nums@.subrange(0, k as int).contains(old(nums)[i as int]));
            } else {
                // current_val == prev_val, so it's already in nums[0..k]
                assert(nums[(k - 1) as int] == current_val);
                assert(current_val == old(nums)[i as int]);
                // Since prev_val is in nums[0..k-1] and prev_val == current_val
                assert(nums@.subrange(0, k as int).contains(old(nums)[i as int]));
            }
        }
        
        i = i + 1;
    }

    // Final assertions to help verify postconditions
    proof {
        assert(i == nums.len());
        assert(forall|j: int| 0 <= j < old(nums).len() ==> 
            nums@.subrange(0, k as int).contains(#[trigger] old(nums)@[j]));
    }

    k
}
// </vc-code>

fn main() {
}

}