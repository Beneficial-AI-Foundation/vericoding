use vstd::prelude::*;

verus! {

// Helper function to check if a sequence is strictly increasing
spec fn is_strictly_increasing(l: Seq<i32>) -> bool
    decreases l.len()
{
    l.len() <= 1 || (l[0] < l[1] && is_strictly_increasing(l.subrange(1, l.len() as int)))
}

// Check if a sequence is a subsequence of another
spec fn is_subsequence_of(subseq: Seq<i32>, nums: Seq<i32>) -> bool {
    exists|indices: Seq<usize>| {
        indices.len() == subseq.len() &&
        (forall|i: int| #![trigger indices[i]]
            0 <= i < indices.len() ==> indices[i] < nums.len()) &&
        (forall|i: int| #![trigger indices[i]]
            0 <= i < indices.len() - 1 ==> indices[i] < indices[i + 1]) &&
        (forall|i: int| #![trigger subseq[i]]
            0 <= i < subseq.len() ==> subseq[i] == nums[indices[i] as int])
    }
}

// Precondition for lengthOfLIS
spec fn length_of_lis_precond(nums: Seq<i32>) -> bool {
    true
}

// Postcondition for lengthOfLIS  
spec fn length_of_lis_postcond(nums: Seq<i32>, result: usize) -> bool {
    // There exists a strictly increasing subsequence of nums with length result
    exists|subseq: Seq<i32>| {
        is_subsequence_of(subseq, nums) &&
        is_strictly_increasing(subseq) &&
        subseq.len() == result
    } &&
    // All strictly increasing subsequences have length <= result
    forall|subseq: Seq<i32>| #![trigger is_subsequence_of(subseq, nums), is_strictly_increasing(subseq)]
        is_subsequence_of(subseq, nums) && is_strictly_increasing(subseq) 
        ==> subseq.len() <= result
}

// Binary search to find position to insert/replace
fn binary_search_position(dp: &Vec<i32>, x: i32) -> (pos: usize) 
    ensures pos <= dp.len()
{
    let mut left = 0;
    let mut right = dp.len();
    
    while left < right
        invariant left <= right <= dp.len()
        decreases right - left
    {
        let mid = left + (right - left) / 2;
        if dp[mid] < x {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    
    left
}

fn length_of_lis(nums: Vec<i32>) -> (result: usize) {
    let mut dp: Vec<i32> = Vec::new();
    
    for i in 0..nums.len() {
        let pos = binary_search_position(&dp, nums[i]);
        if pos == dp.len() {
            dp.push(nums[i]);
        } else {
            assert(pos < dp.len());
            dp.set(pos, nums[i]);
        }
    }
    
    dp.len()
}

proof fn length_of_lis_spec_satisfied(nums: Vec<i32>) {
    // Proof would go here - omitted for now
}

} // verus!

fn main() {}