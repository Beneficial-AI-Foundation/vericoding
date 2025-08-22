use vstd::prelude::*;

verus! {

// Precondition for the longest good subarray function  
spec fn longest_good_subarray_precond(nums: Seq<u32>, k: u32) -> bool {
    true
}

// Helper function to count occurrences of an element in a sequence
spec fn count_occurrences(seq: Seq<u32>, elem: u32) -> nat
    decreases seq.len()
{
    if seq.len() == 0 {
        0
    } else if seq[0] == elem {
        1 + count_occurrences(seq.subrange(1, seq.len() as int), elem)
    } else {
        count_occurrences(seq.subrange(1, seq.len() as int), elem)
    }
}

// Check if a subarray is valid (all frequencies <= k)
spec fn is_valid_subarray(subarray: Seq<u32>, k: u32) -> bool {
    forall|elem: u32| #![auto] count_occurrences(subarray, elem) <= k
}

// Postcondition
spec fn longest_good_subarray_postcond(nums: Seq<u32>, k: u32, result: u32) -> bool {
    if nums.len() == 0 {
        result == 0
    } else {
        // There exists a valid subarray of length result
        (exists|start: int, end: int| #![auto]
            0 <= start <= end <= nums.len() &&
            is_valid_subarray(nums.subrange(start, end), k) &&
            (end - start) == result) &&
        // All valid subarrays have length <= result  
        (forall|start: int, end: int| #![auto]
            0 <= start <= end <= nums.len() &&
            is_valid_subarray(nums.subrange(start, end), k) ==>
            (end - start) <= result)
    }
}

fn longest_good_subarray(nums: Vec<u32>, k: u32) -> (result: u32)
    requires longest_good_subarray_precond(nums@, k)
    ensures longest_good_subarray_postcond(nums@, k, result)
{
    if nums.len() == 0 {
        return 0;
    }
    
    if k == 0 {
        return 0;
    }

    let mut max_len: u32 = 0;
    let n = nums.len();
    
    // Try all possible subarrays
    let mut start = 0;
    while start < n
        invariant 
            0 <= start <= n,
            // max_len is achievable
            exists|s: int, e: int| #![auto]
                0 <= s <= e <= nums.len() &&
                is_valid_subarray(nums@.subrange(s, e), k) &&
                (e - s) == max_len,
            // max_len is optimal among checked subarrays
            forall|s: int, e: int| #![auto]
                0 <= s < start && s <= e <= nums.len() &&
                is_valid_subarray(nums@.subrange(s, e), k) ==>
                (e - s) <= max_len
    {
        let mut freq_map: Map<u32, u32> = Map::empty();
        let mut end = start;
        
        while end < n
            invariant
                start <= end <= n,
                0 <= start <= n,
                // max_len properties preserved
                exists|s: int, e: int| #![auto]
                    0 <= s <= e <= nums.len() &&
                    is_valid_subarray(nums@.subrange(s, e), k) &&
                    (e - s) == max_len,
                forall|s: int, e: int| #![auto]
                    0 <= s < start && s <= e <= nums.len() &&
                    is_valid_subarray(nums@.subrange(s, e), k) ==>
                    (e - s) <= max_len,
                // Current subarray [start, end) satisfies frequency constraint
                forall|elem: u32| #![auto]
                    freq_map.contains_key(elem) ==> 
                    freq_map[elem] <= k
        {
            let current_elem = nums[end];
            let current_count = if freq_map.contains_key(current_elem) {
                freq_map[current_elem]
            } else {
                0
            };
            
            if current_count >= k {
                break;
            }
            
            freq_map = freq_map.insert(current_elem, current_count + 1);
            end += 1;
            
            let current_len = (end - start) as u32;
            if current_len > max_len {
                max_len = current_len;
            }
        }
        
        start += 1;
    }
    
    max_len
}

// Theorem matching the original Lean structure
proof fn longest_good_subarray_spec_satisfied(nums: Vec<u32>, k: u32) 
    requires longest_good_subarray_precond(nums@, k)
{
    let result = longest_good_subarray(nums, k);
    assert(longest_good_subarray_postcond(nums@, k, result));
}

} // verus!

fn main() {
    let nums = vec![1, 2, 1, 2, 3];
    let k = 2;
    let result = longest_good_subarray(nums, k);
    println!("Longest good subarray length: {}", result);
}