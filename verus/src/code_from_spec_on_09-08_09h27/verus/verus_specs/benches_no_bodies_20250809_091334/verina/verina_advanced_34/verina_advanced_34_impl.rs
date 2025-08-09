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
    
    let mut dp = Vec::<i32>::new();
    let mut i = 0;
    
    // Initialize dp array with all 1s (each element forms a subsequence of length 1)
    /* code modified by LLM (iteration 1): added decreases clause */
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            dp.len() == i,
            forall|k: int| 0 <= k < i ==> dp@[k] == 1
        decreases nums.len() - i
    {
        dp.push(1);
        i = i + 1;
    }
    
    // Fill dp array using dynamic programming
    let mut i = 1;
    /* code modified by LLM (iteration 2): added trigger annotation to fix quantifier inference error */
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            dp.len() == nums.len(),
            forall|k: int| #![trigger dp@[k]] 0 <= k < dp.len() ==> 1 <= dp@[k] <= k + 1,
            forall|k: int| 0 <= k < dp.len() ==> dp@[k] <= nums.len()
        decreases nums.len() - i
    {
        let mut j = 0;
        /* code modified by LLM (iteration 2): added trigger annotation to fix quantifier inference error */
        while j < i
            invariant
                0 <= j <= i < nums.len(),
                dp.len() == nums.len(),
                forall|k: int| #![trigger dp@[k]] 0 <= k < dp.len() ==> 1 <= dp@[k] <= k + 1,
                forall|k: int| 0 <= k < dp.len() ==> dp@[k] <= nums.len()
            decreases i - j
        {
            if nums[j] < nums[i] && dp[j] + 1 > dp[i] {
                /* code modified by LLM (iteration 1): store dp[j] value before mutable borrow to fix borrow checker error */
                let dp_j_value = dp[j];
                dp.set(i, dp_j_value + 1);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    // Find the maximum value in dp array
    let mut max_length = 1;
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause */
    while i < dp.len()
        invariant
            0 <= i <= dp.len(),
            dp.len() == nums.len(),
            1 <= max_length <= nums.len(),
            forall|k: int| 0 <= k < i ==> dp@[k] <= max_length,
            exists|k: int| 0 <= k < dp.len() ==> dp@[k] == max_length
        decreases dp.len() - i
    {
        if dp[i] > max_length {
            max_length = dp[i];
        }
        i = i + 1;
    }
    
    max_length
}

} // verus!

fn main() {}