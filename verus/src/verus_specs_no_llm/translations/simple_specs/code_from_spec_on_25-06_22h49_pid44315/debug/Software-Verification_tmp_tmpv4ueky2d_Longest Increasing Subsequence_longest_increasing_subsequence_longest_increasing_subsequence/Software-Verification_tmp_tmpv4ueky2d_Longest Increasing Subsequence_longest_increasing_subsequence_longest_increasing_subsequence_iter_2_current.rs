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
            forall|j: int| 0 <= j < i ==> dp.spec_index(j) >= 1
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
            forall|j: int| 0 <= j < i ==> {
                dp.spec_index(j) == longest_lis_ending_at(nums@, j)
            }
    {
        let mut j = 0;
        while j < i
            invariant
                0 <= j <= i < nums.len(),
                dp.len() == nums.len(),
                forall|k: int| 0 <= k < nums.len() ==> dp.spec_index(k) >= 1,
                forall|k: int| 0 <= k < i ==> {
                    dp.spec_index(k) == longest_lis_ending_at(nums@, k)
                }
        {
            if nums[j] < nums[i] && dp[j] + 1 > dp[i] {
                dp.set(i, dp[j] + 1);
            }
            j += 1;
        }
        i += 1;
    }
    
    // Find maximum value in dp array
    let mut max_len = 1;
    i = 0;
    while i < dp.len()
        invariant
            0 <= i <= dp.len(),
            dp.len() == nums.len(),
            max_len >= 1,
            forall|j: int| 0 <= j < i ==> dp.spec_index(j) <= max_len,
            exists|j: int| 0 <= j < nums.len() ==> dp.spec_index(j) == max_len
    {
        if dp[i] > max_len {
            max_len = dp[i];
        }
        i += 1;
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

// Simplified helper spec function to define the longest LIS ending at a specific position
spec fn longest_lis_ending_at(nums: Seq<int>, pos: int) -> int
    recommends 0 <= pos < nums.len()
    decreases pos
{
    if pos == 0 {
        1
    } else {
        let mut max_prev = 0;
        let mut j = 0;
        while j < pos
            invariant 
                0 <= j <= pos,
                max_prev >= 0
        {
            if nums.spec_index(j) < nums.spec_index(pos) {
                let lis_at_j = longest_lis_ending_at(nums, j);
                if lis_at_j > max_prev {
                    max_prev = lis_at_j;
                }
            }
            j += 1;
        }
        max_prev + 1
    }
}

// Helper spec function to get maximum LIS length ending at any position up to pos
spec fn max_lis_up_to(nums: Seq<int>, pos: int) -> int
    recommends 0 <= pos < nums.len()
    decreases pos
{
    if pos == 0 {
        longest_lis_ending_at(nums, 0)
    } else {
        let current = longest_lis_ending_at(nums, pos);
        let prev_max = max_lis_up_to(nums, pos - 1);
        if current > prev_max { current } else { prev_max }
    }
}

}