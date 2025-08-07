use vstd::prelude::*;

verus! {

// Precondition for lengthOfLIS  
spec fn length_of_lis_precond(nums: Vec<i32>) -> bool {
    true
}

// Check if a sequence is strictly increasing
spec fn is_strictly_increasing(seq: Vec<i32>) -> bool {
    forall |i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] < seq[j]
}

// Generate all subsequences (abstracted function)
spec fn all_subsequences(nums: Vec<i32>) -> Set<Vec<i32>>
{
    arbitrary()
}

// Postcondition for lengthOfLIS matching the original Lean specification
spec fn length_of_lis_postcond(nums: Vec<i32>, result: usize) -> bool {
    let all_subseq = all_subsequences(nums);
    let increasing_subseqs = all_subseq.filter(|seq: Vec<i32>| is_strictly_increasing(seq));
    let increasing_lens = increasing_subseqs.map(|seq: Vec<i32>| seq.len());
    
    increasing_lens.contains(result) && 
    (forall |len: usize| increasing_lens.contains(len) ==> len <= result)
}

// Helper function to find maximum in array, similar to Lean's maxInArray
fn max_in_array(arr: Vec<usize>) -> (result: usize)
{
    if arr.len() == 0 {
        0
    } else {
        let mut max_val = arr[0];
        for i in 1..arr.len() {
            if arr[i] > max_val {
                max_val = arr[i];
            }
        }
        max_val
    }
}

// Main function implementation matching the original Lean algorithm
fn length_of_lis(nums: Vec<i32>) -> (result: usize)
    requires length_of_lis_precond(nums),
{
    if nums.len() == 0 {
        0
    } else {
        let n = nums.len();
        let mut dp: Vec<usize> = Vec::with_capacity(n);
        
        // Initialize dp array with 1s (each element forms LIS of length 1)
        for i in 0..n
            invariant dp.len() == i,
        {
            dp.push(1);
        }
        
        // Dynamic programming - for each position i, check all previous positions j
        for i in 1..n
            invariant 
                dp.len() == n,
                1 <= i <= n,
        {
            for j in 0..i
                invariant 
                    dp.len() == n,
                    1 <= i < n,
                    0 <= j <= i,
            {
                // If nums[j] < nums[i], we can extend the LIS ending at j
                if j < nums.len() && i < nums.len() && j < dp.len() && i < dp.len() &&
                   nums[j] < nums[i] && dp[j] < usize::MAX && dp[j] + 1 > dp[i] {
                    dp[i] = dp[j] + 1;
                }
            }
        }
        
        // Return the maximum value in dp array
        max_in_array(dp)
    }
}

} // verus!

fn main() {
}