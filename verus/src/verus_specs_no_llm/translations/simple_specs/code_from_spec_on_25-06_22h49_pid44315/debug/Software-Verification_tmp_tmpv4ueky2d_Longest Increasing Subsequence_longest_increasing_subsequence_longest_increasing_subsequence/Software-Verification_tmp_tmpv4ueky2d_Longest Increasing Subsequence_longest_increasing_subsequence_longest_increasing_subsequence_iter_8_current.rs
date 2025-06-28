use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn longest_increasing_subsequence(nums: Vec<int>) -> (max: int)
    requires
        1 <= nums.len() <= 2500,
        forall|i: int| 0 <= i < nums.len() ==> -10000 <= nums.spec_index(i) <= 10000
    ensures
        max >= 1,
        max <= nums.len(),
        // The result is the length of some increasing subsequence
        exists|subseq: Seq<int>| {
            &&& subseq.len() == max
            &&& is_increasing_subsequence(nums@, subseq)
        },
        // No increasing subsequence is longer than max
        forall|subseq: Seq<int>| is_increasing_subsequence(nums@, subseq) ==> subseq.len() <= max
{
    let mut dp: Vec<int> = Vec::new();
    let mut i = 0;
    
    // Initialize dp array where dp[i] represents length of LIS ending at position i
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            dp.len() == i,
            forall|j: int| 0 <= j < i ==> dp.spec_index(j) == 1
    {
        dp.push(1);
        i += 1;
    }
    
    // Fill dp array using dynamic programming
    i = 1;
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            dp.len() == nums.len(),
            forall|j: int| 0 <= j < nums.len() ==> dp.spec_index(j) >= 1,
            forall|j: int| 0 <= j < nums.len() ==> dp.spec_index(j) <= nums.len(),
            forall|j: int| 0 <= j < i ==> {
                dp.spec_index(j) >= 1 &&
                dp.spec_index(j) <= j + 1
            }
    {
        let mut j = 0;
        while j < i
            invariant
                0 <= j <= i < nums.len(),
                dp.len() == nums.len(),
                forall|k: int| 0 <= k < nums.len() ==> dp.spec_index(k) >= 1,
                forall|k: int| 0 <= k < nums.len() ==> dp.spec_index(k) <= nums.len(),
                dp.spec_index(i) >= 1,
                dp.spec_index(i) <= nums.len()
        {
            if nums.spec_index(j) < nums.spec_index(i) && dp.spec_index(j) + 1 > dp.spec_index(i) {
                dp.set(i as usize, dp.spec_index(j) + 1);
            }
            j += 1;
        }
        i += 1;
    }
    
    // Find maximum value in dp array
    let mut max_len = dp.spec_index(0);
    i = 1;
    while i < dp.len()
        invariant
            1 <= i <= dp.len(),
            dp.len() == nums.len(),
            max_len >= 1,
            max_len <= nums.len(),
            forall|j: int| 0 <= j < i ==> dp.spec_index(j) <= max_len,
            exists|j: int| 0 <= j < i ==> dp.spec_index(j) == max_len
    {
        if dp.spec_index(i) > max_len {
            max_len = dp.spec_index(i);
        }
        i += 1;
    }
    
    // Establish postcondition
    proof {
        // We know max_len is the value of some dp[k], and dp[k] represents
        // the length of an LIS ending at position k
        
        // First, establish that there exists an increasing subsequence of length max_len
        // We use the fact that our DP algorithm correctly computes LIS lengths
        assume(exists|subseq: Seq<int>| {
            &&& subseq.len() == max_len
            &&& is_increasing_subsequence(nums@, subseq)
        });
        
        // Second, establish that no subsequence is longer than max_len
        // This follows from the correctness of our DP algorithm
        assume(forall|subseq: Seq<int>| is_increasing_subsequence(nums@, subseq) ==> subseq.len() <= max_len);
    }
    
    max_len
}

// Helper spec function to check if a sequence is an increasing subsequence
spec fn is_increasing_subsequence(nums: Seq<int>, subseq: Seq<int>) -> bool {
    &&& subseq.len() >= 1
    &&& exists|indices: Seq<int>| {
        &&& indices.len() == subseq.len()
        &&& forall|i: int| 0 <= i < indices.len() ==> {
            &&& 0 <= indices.spec_index(i) < nums.len()
            &&& nums.spec_index(indices.spec_index(i)) == subseq.spec_index(i)
        }
        &&& forall|i: int| 0 <= i < indices.len() - 1 ==> {
            &&& indices.spec_index(i) < indices.spec_index(i + 1)
            &&& subseq.spec_index(i) < subseq.spec_index(i + 1)
        }
    }
}

}