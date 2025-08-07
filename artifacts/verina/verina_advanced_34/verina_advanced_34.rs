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
    
    let mut sub: Vec<i32> = Vec::new();
    sub.push(nums[0]);
    
    let mut i = 1;
    while i < nums.len()
        invariant 
            1 <= i <= nums.len(),
            sub.len() > 0,
            sub.len() <= i,
        decreases nums.len() - i
    {
        let num = nums[i];
        let sub_len = sub.len();
        
        if num > sub[sub_len - 1] {
            sub.push(num);
        } else {
            // Binary search to find the position to replace
            let mut left: usize = 0;
            let mut right: usize = sub_len;
            
            while left < right
                invariant 
                    left <= right <= sub.len(),
                    sub.len() > 0,
                decreases right - left
            {
                let mid = left + (right - left) / 2;
                
                if sub[mid] < num {
                    left = mid + 1;
                } else {
                    right = mid;
                }
            }
            
            if left < sub.len() {
                sub.set(left, num);
            }
        }
        
        i += 1;
    }
    
    assert(sub.len() <= nums.len());
    sub.len() as i32
}

} // verus!

fn main() {
    // Test the function
    let nums = vec![10, 9, 2, 5, 3, 7, 101, 18];
    let result = longest_increasing_subsequence(nums);
    println!("Result: {}", result);
}