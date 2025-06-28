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

fn largest_sum(nums: Vec<int>, k: int) -> (sum: int)
    requires
        nums.len() > 0
    ensures
        max_sum_subarray(nums, sum, 0, nums.len())
{
    let mut max_sum = nums[0];
    let mut current_sum = nums[0];
    
    let mut i = 1;
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            nums.len() > 0,
            // max_sum is achievable by some subarray in range [0, i]
            exists |u: int, v: int| 0 <= u && u <= v && v <= i && Sum_Array(nums, u, v) == max_sum,
            // max_sum is maximum among all subarrays in range [0, i]
            forall |u: int, v: int| 0 <= u && u <= v && v <= i ==> Sum_Array(nums, u, v) <= max_sum,
            // current_sum represents max sum ending at position i-1
            current_sum == max_ending_here(nums, i as int)
    {
        // Update current_sum to be max sum ending at position i
        current_sum = if current_sum > 0 { current_sum + nums[i] } else { nums[i] };
        
        // Update max_sum if current_sum is larger
        if current_sum > max_sum {
            max_sum = current_sum;
        }
        
        i += 1;
    }
    
    max_sum
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
    assert(Sum_Array(arr, i, i + 1) == arr[i] + Sum_Array(arr, i, i));
    assert(Sum_Array(arr, i, i) == 0);
}

// Helper lemma for subarray properties
proof fn lemma_sum_array_extend(arr: Vec<int>, start: int, stop: int)
    requires 0 <= start <= stop < arr.len()
    ensures Sum_Array(arr, start, stop + 1) == Sum_Array(arr, start, stop) + arr[stop]
{
    // This follows from the recursive definition of Sum_Array
    if start == stop {
        assert(Sum_Array(arr, start, stop) == 0);
        lemma_sum_array_single(arr, stop);
        assert(Sum_Array(arr, start, stop + 1) == arr[stop]);
    } else {
        lemma_sum_array_extend(arr, start, stop - 1);
    }
}

// Basic lemma about non-empty subarrays
proof fn lemma_sum_array_bounds(arr: Vec<int>, start: int, stop: int)
    requires 0 <= start < stop <= arr.len()
    ensures Sum_Array(arr, start, stop) >= arr[stop - 1] - Sum_Array(arr, start, stop - 1).abs()
{
    // Basic property that follows from definition
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
        if prev_ending > 0 {
            lemma_max_ending_here_achievable(arr, end - 1);
            // There exists a start for end-1, extend it
            assert(exists |start: int| 0 <= start < end - 1 && Sum_Array(arr, start, end - 1) == prev_ending);
            // Use that start to show the property for end
        } else {
            lemma_sum_array_single(arr, end - 1);
        }
    }
}

// Simplified proof structure
proof fn lemma_kadane_correctness(arr: Vec<int>, i: int)
    requires 0 < i <= arr.len()
    ensures 
        exists |u: int, v: int| 0 <= u && u <= v && v <= i && Sum_Array(arr, u, v) == max_ending_here(arr, i),
        forall |start: int| 0 <= start < i ==> Sum_Array(arr, start, i) <= max_ending_here(arr, i)
    decreases i
{
    if i == 1 {
        lemma_sum_array_single(arr, 0);
    } else {
        lemma_kadane_correctness(arr, i - 1);
        lemma_max_ending_here_achievable(arr, i);
        lemma_max_ending_here_is_max(arr, i);
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
        let prev_ending = max_ending_here(arr, end - 1);
        
        // For any start < end, either start == end-1 (single element) 
        // or we can use inductive hypothesis
        assert(forall |start: int| 0 <= start < end ==> {
            if start == end - 1 {
                Sum_Array(arr, start, end) == arr[end - 1]
            } else {
                Sum_Array(arr, start, end - 1) <= prev_ending
            }
        });
    }
}

}