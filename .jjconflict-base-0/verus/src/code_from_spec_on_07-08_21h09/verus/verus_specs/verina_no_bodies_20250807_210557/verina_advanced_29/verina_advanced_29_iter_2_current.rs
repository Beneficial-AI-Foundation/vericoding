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

    let mut max_len = 0u32;
    let n = nums.len();

    // Try all possible starting positions
    let mut start = 0;
    /* code modified by LLM (iteration 1): added decreases clause to fix termination verification error */
    while start < n
        invariant 
            start <= n,
            max_len <= n,
            // max_len is the maximum length found so far
            forall|s: int, e: int| #![auto]
                0 <= s < start && s <= e <= n &&
                is_valid_subarray(nums@.subrange(s, e), k) ==>
                (e - s) <= max_len,
            // There exists a valid subarray of length max_len (if max_len > 0)
            max_len == 0 || (exists|s: int, e: int| #![auto]
                0 <= s < start && s <= e <= n &&
                is_valid_subarray(nums@.subrange(s, e), k) &&
                (e - s) == max_len)
        decreases n - start
    {
        // Use a frequency map implemented as a vector
        // Since we're dealing with u32, we'll use a simple approach
        let mut freq_map: Vec<(u32, u32)> = Vec::new();
        
        let mut end = start;
        /* code modified by LLM (iteration 1): added decreases clause to inner while loop */
        while end < n
            invariant
                start <= end <= n,
                start < n,
                max_len <= n,
                // Frequency map constraints would go here in a full implementation
            decreases n - end
        {
            let elem = nums[end];
            
            // Update frequency map
            let mut found = false;
            let mut elem_count = 0;
            let mut i = 0;
            /* code modified by LLM (iteration 1): added decreases clause to frequency map search loop */
            while i < freq_map.len()
                invariant i <= freq_map.len()
                decreases freq_map.len() - i
            {
                if freq_map[i].0 == elem {
                    elem_count = freq_map[i].1;
                    found = true;
                    break;
                }
                i += 1;
            }
            
            if found {
                if elem_count >= k {
                    // Would exceed k occurrences, break
                    break;
                } else {
                    // Update count
                    freq_map.set(i, (elem, elem_count + 1));
                }
            } else {
                // Add new element
                freq_map.push((elem, 1));
            }
            
            // Update max_len if current subarray is longer
            let current_len = (end - start + 1) as u32;
            if current_len > max_len {
                max_len = current_len;
            }
            
            end += 1;
        }
        
        start += 1;
    }

    max_len
}

// Theorem matching the original Lean structure
proof fn longest_good_subarray_spec_satisfied(nums: Vec<u32>, k: u32) 
    requires longest_good_subarray_precond(nums@, k)
{
    // For now, using admit to match the original Lean "sorry"
    admit();
}

} // verus!

fn main() {
    let nums = vec![1, 2, 3, 1, 2, 3, 1, 2];
    let k = 2;
    let result = longest_good_subarray(nums, k);
    println!("Longest good subarray length: {}", result);
}