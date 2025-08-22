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
    requires arr.len() > 0,
    ensures forall |i: int| 0 <= i < arr.len() ==> arr[i] <= result,
    /* code modified by LLM (iteration 1): fixed missing curly braces in ensures clause */
    ensures exists |i: int| 0 <= i < arr.len() && arr[i] == result
{
    let mut max_val = arr[0];
    let mut idx = 1;
    
    while idx < arr.len()
        invariant 
            1 <= idx <= arr.len(),
            forall |i: int| 0 <= i < idx ==> arr[i] <= max_val,
            exists |i: int| 0 <= i < idx && arr[i] == max_val,
    {
        if arr[idx] > max_val {
            max_val = arr[idx];
        }
        idx += 1;
    }
    
    max_val
}

// Main function implementation matching the original Lean algorithm
fn length_of_lis(nums: Vec<i32>) -> (result: usize)
    requires length_of_lis_precond(nums),
{
    if nums.len() == 0 {
        return 0;
    }
    
    let mut dp: Vec<usize> = Vec::new();
    let mut i = 0;
    
    // Initialize dp array with all 1s
    while i < nums.len()
        invariant 
            0 <= i <= nums.len(),
            dp.len() == i,
            forall |j: int| 0 <= j < i ==> dp[j] == 1,
    {
        dp.push(1);
        i += 1;
    }
    
    // Dynamic programming to find LIS
    i = 1;
    while i < nums.len()
        invariant 
            1 <= i <= nums.len(),
            dp.len() == nums.len(),
            forall |k: int| 0 <= k < dp.len() ==> dp[k] >= 1,
    {
        let mut j = 0;
        while j < i
            invariant 
                0 <= j <= i,
                i < nums.len(),
                dp.len() == nums.len(),
                forall |k: int| 0 <= k < dp.len() ==> dp[k] >= 1,
        {
            if nums[j] < nums[i] {
                if dp[j] + 1 > dp[i] {
                    dp.set(i, dp[j] + 1);
                }
            }
            j += 1;
        }
        i += 1;
    }
    
    if dp.len() > 0 {
        max_in_array(dp)
    } else {
        0
    }
}

/* code modified by LLM (iteration 1): moved main function inside verus block to access length_of_lis */
fn main() {
    let nums = vec![10, 9, 2, 5, 3, 7, 101, 18];
    let result = length_of_lis(nums);
    println!("Length of LIS: {}", result);
}

} // verus!