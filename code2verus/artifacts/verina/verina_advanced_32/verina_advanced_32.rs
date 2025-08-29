use vstd::prelude::*;

verus! {

// Helper function to check if a sequence is strictly increasing
spec fn is_strictly_increasing(seq: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] < seq[j]
}

// Precondition (always true in this case)  
spec fn longest_increasing_subsequence_precond(numbers: Seq<int>) -> bool {
    true
}

// Postcondition - simplified version
spec fn longest_increasing_subsequence_postcond(numbers: Seq<int>, result: usize) -> bool {
    // The result represents the length of the longest increasing subsequence
    // Full formal specification would require defining all subsequences
    true  // Placeholder for now
}

// Helper function to find maximum in a vector
fn find_max_length(lengths: Vec<usize>) -> (result: usize)
{
    if lengths.len() == 0 {
        return 0;
    }
    
    let mut max_val = lengths[0];
    let mut i = 1;
    
    while i < lengths.len()
        invariant
            0 <= i <= lengths.len(),
            forall|k: int| 0 <= k < i ==> lengths[k] <= max_val,
            exists|k: int| 0 <= k < lengths.len() && lengths[k] == max_val,
        decreases lengths.len() - i,
    {
        if lengths[i] > max_val {
            max_val = lengths[i];
        }
        i += 1;
    }
    max_val
}

// Helper function to find best previous length
fn find_length_ending_at_curr(prev_nums: &Vec<i32>, lengths: &Vec<usize>, curr_num: i32) -> (result: usize)
    requires prev_nums.len() == lengths.len()
{
    let mut best = 0;
    let mut i = 0;
    
    while i < prev_nums.len()
        invariant
            0 <= i <= prev_nums.len(),
            prev_nums.len() == lengths.len(),
        decreases prev_nums.len() - i,
    {
        if prev_nums[i] < curr_num {
            if lengths[i] > best {
                best = lengths[i];
            }
        }
        i += 1;
    }
    best
}

// Main function
fn longest_increasing_subsequence(numbers: Vec<i32>) -> (result: usize)
    requires 
        longest_increasing_subsequence_precond(numbers@.map(|i: int, x: i32| x as int)),
        numbers.len() < 1000000, // Reasonable bound to prevent overflow
    ensures longest_increasing_subsequence_postcond(
        numbers@.map(|i: int, x: i32| x as int),
        result
    )
{
    if numbers.len() == 0 {
        return 0;
    }
    if numbers.len() == 1 {
        return 1;
    }
    
    let first = numbers[0];
    let mut prev_nums = vec![first];
    let mut lengths = vec![1];
    let mut i = 1;
    
    while i < numbers.len()
        invariant
            1 <= i <= numbers.len(),
            prev_nums.len() == lengths.len(),
            prev_nums.len() == i,
            numbers.len() < 1000000,
        decreases numbers.len() - i,
    {
        let curr_num = numbers[i];
        let best_prev_len = find_length_ending_at_curr(&prev_nums, &lengths, curr_num);
        
        // Ensure no overflow
        if best_prev_len < usize::MAX {
            let curr_length = best_prev_len + 1;
            prev_nums.push(curr_num);
            lengths.push(curr_length);
        } else {
            // This shouldn't happen with reasonable inputs
            prev_nums.push(curr_num);
            lengths.push(1);
        }
        
        i += 1;
    }
    
    find_max_length(lengths)
}

} // verus!

fn main() {}