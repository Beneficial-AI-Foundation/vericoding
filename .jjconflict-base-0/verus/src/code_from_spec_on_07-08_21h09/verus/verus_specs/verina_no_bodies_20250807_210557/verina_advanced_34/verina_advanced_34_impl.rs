use vstd::prelude::*;

verus! {

// Precondition for longest increasing subsequence
spec fn longest_increasing_subsequence_precond(nums: Seq<i32>) -> bool {
    true
}

// Helper function to check if a sequence is strictly increasing
spec fn is_strictly_increasing(seq: Seq<i32>) -> bool {
    forall|i: int, j: int| #![auto] 0 <= i < j < seq.len() ==> seq[i] < seq[j]
}

// Helper function to check if a sequence is a subsequence of another
spec fn is_subsequence(subseq: Seq<i32>, seq: Seq<i32>) -> bool {
    exists|indices: Seq<int>| #![auto]
        indices.len() == subseq.len() &&
        (forall|i: int| #![auto] 0 <= i < indices.len() ==> 
            0 <= indices[i] < seq.len() &&
            seq[indices[i]] == subseq[i]) &&
        (forall|i: int, j: int| #![auto] 0 <= i < j < indices.len() ==> 
            indices[i] < indices[j])
}

// Postcondition - result should be non-negative and at most the length of input
spec fn longest_increasing_subsequence_postcond(
    nums: Seq<i32>, 
    result: i32
) -> bool {
    0 <= result <= nums.len()
}

fn longest_increasing_subsequence(nums: Vec<i32>) -> (result: i32)
    requires 
        longest_increasing_subsequence_precond(nums@),
        nums.len() <= i32::MAX
    ensures longest_increasing_subsequence_postcond(nums@, result)
{
    if nums.len() == 0 {
        return 0;
    }
    
    let mut dp: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for outer loop termination */
    while i < nums.len()
        invariant
            i <= nums.len(),
            dp.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> dp@[j] >= 1,
            forall|j: int| #![auto] 0 <= j < i ==> dp@[j] <= j + 1
        decreases nums.len() - i
    {
        let mut max_len = 1;
        let mut j: usize = 0;
        
        /* code modified by LLM (iteration 1): added decreases clause for inner loop termination */
        while j < i
            invariant
                j <= i,
                i < nums.len(),
                dp.len() == i,
                max_len >= 1,
                max_len <= i + 1,
                forall|k: int| #![auto] 0 <= k < i ==> dp@[k] >= 1,
                forall|k: int| #![auto] 0 <= k < i ==> dp@[k] <= k + 1
            decreases i - j
        {
            if nums[j] < nums[i] && dp[j] + 1 > max_len {
                max_len = dp[j] + 1;
            }
            j += 1;
        }
        
        dp.push(max_len);
        i += 1;
    }
    
    let mut max_result = 1;
    let mut k: usize = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for final loop termination */
    while k < dp.len()
        invariant
            k <= dp.len(),
            dp.len() == nums.len(),
            max_result >= 1,
            max_result <= nums.len(),
            forall|j: int| #![auto] 0 <= j < dp.len() ==> dp@[j] >= 1,
            forall|j: int| #![auto] 0 <= j < dp.len() ==> dp@[j] <= nums.len()
        decreases dp.len() - k
    {
        if dp[k] > max_result {
            max_result = dp[k];
        }
        k += 1;
    }
    
    max_result
}

} // verus!

fn main() {
    let nums = vec![10, 9, 2, 5, 3, 7, 101, 18];
    let result = longest_increasing_subsequence(nums);
    println!("Length of longest increasing subsequence: {}", result);
}