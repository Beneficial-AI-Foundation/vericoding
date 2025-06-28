use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn max_sum_subarray(arr: Vec<int>, sum: int, start: int, stop: int) -> bool
{
    arr.len() > 0 &&
    0 <= start <= stop <= arr.len() &&
    (forall |u: int, v: int| start <= u && u <= v && v <= stop ==> Sum_Array(arr, u, v) <= sum) &&
    (exists |u: int, v: int| start <= u && u <= v && v <= stop && Sum_Array(arr, u, v) == sum)
}

spec fn Sum_Array(arr: Vec<int>, start: int, stop: int) -> int
    requires 0 <= start <= stop <= arr.len()
    decreases stop - start
{
    if start >= stop { 
        0 
    } else { 
        arr[stop - 1] + Sum_Array(arr, start, stop - 1) 
    }
}

spec fn max_ending_here(arr: Vec<int>, end: int) -> int
    requires 0 < end <= arr.len()
    decreases end
{
    if end == 1 {
        arr[0]
    } else {
        let prev_ending = max_ending_here(arr, end - 1);
        if prev_ending > 0 { prev_ending + arr[end - 1] } else { arr[end - 1] }
    }
}

// Helper lemma to establish properties of Sum_Array
proof fn lemma_sum_array_single(arr: Vec<int>, i: int)
    requires 0 <= i < arr.len()
    ensures Sum_Array(arr, i, i + 1) == arr[i]
{
    // Base case of the recursive definition
}

// Helper lemma for subarray properties
proof fn lemma_sum_array_extend(arr: Vec<int>, start: int, stop: int)
    requires 0 <= start <= stop < arr.len()
    ensures Sum_Array(arr, start, stop + 1) == Sum_Array(arr, start, stop) + arr[stop]
{
    // Follows from recursive definition
}

// Lemma connecting max_ending_here to actual subarrays  
proof fn lemma_max_ending_here_achievable(arr: Vec<int>, end: int)
    requires 0 < end <= arr.len()
    ensures exists |start: int| 0 <= start < end && Sum_Array(arr, start, end) == max_ending_here(arr, end)
    decreases end
{
    if end == 1 {
        lemma_sum_array_single(arr, 0);
    } else {
        let prev_ending = max_ending_here(arr, end - 1);
        lemma_max_ending_here_achievable(arr, end - 1);
        
        if prev_ending > 0 {
            // Extend the previous subarray
            let start = choose |s: int| 0 <= s < end - 1 && Sum_Array(arr, s, end - 1) == prev_ending;
            lemma_sum_array_extend(arr, start, end - 1);
        } else {
            // Start new subarray at end-1
            lemma_sum_array_single(arr, end - 1);
        }
    }
}

// Helper lemma for max_ending_here being maximum among subarrays ending at specific position
proof fn lemma_max_ending_here_is_max(arr: Vec<int>, end: int)
    requires 0 < end <= arr.len()
    ensures forall |start: int| 0 <= start < end ==> Sum_Array(arr, start, end) <= max_ending_here(arr, end)
    decreases end
{
    if end == 1 {
        lemma_sum_array_single(arr, 0);
    } else {
        lemma_max_ending_here_is_max(arr, end - 1);
        
        // For any subarray ending at position end
        let forall_closure = |start: int| {
            requires(0 <= start < end);
            ensures(Sum_Array(arr, start, end) <= max_ending_here(arr, end));
            
            if start == end - 1 {
                // Single element subarray
                lemma_sum_array_single(arr, start);
            } else {
                // Multi-element subarray  
                lemma_sum_array_extend(arr, start, end - 1);
            }
        };
        assert_forall_by(forall_closure);
    }
}

proof fn lemma_max_ending_correctness(arr: Vec<int>, end: int)
    requires 0 < end <= arr.len()
    ensures 
        exists |start: int| 0 <= start < end && Sum_Array(arr, start, end) == max_ending_here(arr, end),
        forall |start: int| 0 <= start < end ==> Sum_Array(arr, start, end) <= max_ending_here(arr, end)
{
    lemma_max_ending_here_achievable(arr, end);
    lemma_max_ending_here_is_max(arr, end);
}

fn largest_sum(nums: Vec<int>, k: int) -> (sum: int)
    requires
        nums.len() > 0
    ensures
        max_sum_subarray(nums, sum, 0, nums.len())
{
    let mut max_sum = nums[0];
    let mut current_sum = nums[0];
    
    // Base case proofs
    proof {
        lemma_sum_array_single(nums, 0);
        lemma_max_ending_correctness(nums, 1);
    }
    
    let mut i = 1;
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            nums.len() > 0,
            // max_sum is achievable by some subarray in range [0, i]
            exists |u: int, v: int| 0 <= u && u <= v && v <= (i as int) && Sum_Array(nums, u, v) == max_sum,
            // max_sum is maximum among all subarrays in range [0, i]
            forall |u: int, v: int| 0 <= u && u <= v && v <= (i as int) ==> Sum_Array(nums, u, v) <= max_sum,
            // current_sum represents max sum ending at position i-1
            current_sum == max_ending_here(nums, i as int)
    {
        // Compute next values
        let new_current = if current_sum > 0 { current_sum + nums[i] } else { nums[i] };
        let new_max = if new_current > max_sum { new_current } else { max_sum };
        
        proof {
            // Prove new_current equals max_ending_here at i+1
            assert(new_current == max_ending_here(nums, (i + 1) as int));
            
            // Get properties of max_ending_here at i+1
            lemma_max_ending_correctness(nums, (i + 1) as int);
            
            // Prove new_max maintains invariants
            if new_current > max_sum {
                // new_current is achievable at position i+1
                assert(exists |u: int, v: int| 0 <= u && u <= v && v <= (i + 1) as int && Sum_Array(nums, u, v) == new_current);
                // new_current is maximum among all subarrays ending at i+1, and >= max_sum
                assert(forall |u: int, v: int| 0 <= u && u <= v && v <= (i + 1) as int ==> Sum_Array(nums, u, v) <= new_current);
            } else {
                // max_sum remains the maximum
                assert(forall |u: int, v: int| 0 <= u && u <= v && v <= (i + 1) as int ==> Sum_Array(nums, u, v) <= max_sum);
            }
        }
        
        // Update values
        current_sum = new_current;
        max_sum = new_max;
        i += 1;
    }
    
    max_sum
}

}