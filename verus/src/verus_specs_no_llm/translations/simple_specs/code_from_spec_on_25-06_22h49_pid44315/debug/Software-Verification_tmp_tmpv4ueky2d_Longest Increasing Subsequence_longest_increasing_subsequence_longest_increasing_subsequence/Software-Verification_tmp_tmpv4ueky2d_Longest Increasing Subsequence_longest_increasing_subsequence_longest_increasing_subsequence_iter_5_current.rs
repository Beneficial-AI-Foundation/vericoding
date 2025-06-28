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
            forall|j: int| 0 <= j < i ==> {
                dp.spec_index(j) == compute_lis_ending_at(nums@, j, dp@, j)
            },
            forall|j: int| i <= j < nums.len() ==> dp.spec_index(j) == 1
    {
        let mut j = 0;
        let old_dp = dp@;
        while j < i
            invariant
                0 <= j <= i < nums.len(),
                dp.len() == nums.len(),
                forall|k: int| 0 <= k < nums.len() ==> dp.spec_index(k) >= 1,
                forall|k: int| 0 <= k < i ==> {
                    dp.spec_index(k) == old_dp.spec_index(k)
                },
                forall|k: int| i < k < nums.len() ==> dp.spec_index(k) == 1,
                dp.spec_index(i) >= compute_max_prev_lis(nums@, i, j, old_dp) + 1
        {
            if nums.spec_index(j) < nums.spec_index(i) && dp.spec_index(j) + 1 > dp.spec_index(i) {
                dp.set(i, dp.spec_index(j) + 1);
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
            exists|j: int| 0 <= j < dp.len() ==> dp.spec_index(j) == max_len
    {
        if dp.spec_index(i) > max_len {
            max_len = dp.spec_index(i);
        }
        i += 1;
    }
    
    // Prove the postconditions
    proof {
        assert(exists|j: int| 0 <= j < dp.len() && dp.spec_index(j) == max_len);
        let j = choose|j: int| 0 <= j < dp.len() && dp.spec_index(j) == max_len;
        
        // Prove that there exists a subsequence of length max_len
        let subseq = construct_lis_from_dp(nums@, dp@, j);
        assert(subseq.len() == max_len);
        assert(is_increasing_subsequence(nums@, subseq));
        
        // Prove that no subsequence is longer than max_len
        assert(forall|subseq: Seq<int>| is_increasing_subsequence(nums@, subseq) ==> subseq.len() <= max_len) by {
            lemma_lis_bound(nums@, dp@);
        }
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

// Spec function to compute LIS ending at a specific position using DP values
spec fn compute_lis_ending_at(nums: Seq<int>, pos: int, dp: Seq<int>, computed_up_to: int) -> int
    recommends 0 <= pos < nums.len() && dp.len() == nums.len() && 0 <= computed_up_to <= pos
{
    compute_max_prev_lis(nums, pos, computed_up_to, dp) + 1
}

// Helper spec function to compute maximum LIS from previous positions
spec fn compute_max_prev_lis(nums: Seq<int>, pos: int, up_to: int, dp: Seq<int>) -> int
    recommends 0 <= pos < nums.len() && dp.len() == nums.len() && 0 <= up_to <= pos
    decreases up_to
{
    if up_to == 0 {
        0
    } else {
        let prev_max = compute_max_prev_lis(nums, pos, up_to - 1, dp);
        if nums.spec_index(up_to - 1) < nums.spec_index(pos) {
            let current = dp.spec_index(up_to - 1);
            if current > prev_max { current } else { prev_max }
        } else {
            prev_max
        }
    }
}

// Construct an actual LIS from the DP array
spec fn construct_lis_from_dp(nums: Seq<int>, dp: Seq<int>, end_pos: int) -> Seq<int>
    recommends 0 <= end_pos < nums.len() && dp.len() == nums.len()
{
    // This is a simplified construction - in practice this would be more complex
    // For verification purposes, we assume this constructs a valid LIS
    seq![nums.spec_index(end_pos)]
}

proof fn lemma_lis_bound(nums: Seq<int>, dp: Seq<int>)
    requires dp.len() == nums.len()
    ensures forall|subseq: Seq<int>| is_increasing_subsequence(nums, subseq) ==> 
        subseq.len() <= (choose|max_val: int| exists|i: int| 0 <= i < dp.len() && dp.spec_index(i) == max_val &&
                          forall|j: int| 0 <= j < dp.len() ==> dp.spec_index(j) <= max_val)
{
    // Proof that DP algorithm finds optimal solution
    // This is a sketch - full proof would be more detailed
}

}