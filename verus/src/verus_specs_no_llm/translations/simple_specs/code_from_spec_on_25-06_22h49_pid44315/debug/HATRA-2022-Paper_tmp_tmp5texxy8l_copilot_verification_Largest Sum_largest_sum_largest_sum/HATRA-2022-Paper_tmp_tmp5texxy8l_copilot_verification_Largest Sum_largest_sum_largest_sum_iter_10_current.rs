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
    // Base case of Sum_Array recursive definition
}

// Helper lemma for subarray properties
proof fn lemma_sum_array_extend(arr: Vec<int>, start: int, stop: int)
    requires 0 <= start <= stop < arr.len()
    ensures Sum_Array(arr, start, stop + 1) == Sum_Array(arr, start, stop) + arr[stop]
{
    // Follows from recursive definition of Sum_Array
}

// Lemma connecting max_ending_here to actual subarrays  
proof fn lemma_max_ending_here_achievable(arr: Vec<int>, end: int)
    requires 0 < end <= arr.len()
    ensures exists |start: int| 0 <= start < end && Sum_Array(arr, start, end) == max_ending_here(arr, end)
    decreases end
{
    if end == 1 {
        lemma_sum_array_single(arr, 0);
        assert(Sum_Array(arr, 0, 1) == arr[0]);
        assert(max_ending_here(arr, 1) == arr[0]);
    } else {
        let prev_ending = max_ending_here(arr, end - 1);
        lemma_max_ending_here_achievable(arr, end - 1);
        
        if prev_ending > 0 {
            let start = choose |s: int| 0 <= s < end - 1 && Sum_Array(arr, s, end - 1) == prev_ending;
            lemma_sum_array_extend(arr, start, end - 1);
            assert(Sum_Array(arr, start, end) == prev_ending + arr[end - 1]);
            assert(Sum_Array(arr, start, end) == max_ending_here(arr, end));
        } else {
            lemma_sum_array_single(arr, end - 1);
            assert(Sum_Array(arr, end - 1, end) == arr[end - 1]);
            assert(max_ending_here(arr, end) == arr[end - 1]);
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
        
        assert forall |start: int| 0 <= start < end implies Sum_Array(arr, start, end) <= max_ending_here(arr, end) by {
            lemma_sum_array_extend(arr, start, end - 1);
            let prev_ending = max_ending_here(arr, end - 1);
            
            if start == end - 1 {
                lemma_sum_array_single(arr, start);
                assert(Sum_Array(arr, start, end) == arr[end - 1]);
            } else {
                assert(Sum_Array(arr, start, end - 1) <= prev_ending);
                assert(Sum_Array(arr, start, end) == Sum_Array(arr, start, end - 1) + arr[end - 1]);
                
                if prev_ending > 0 {
                    assert(max_ending_here(arr, end) == prev_ending + arr[end - 1]);
                    assert(Sum_Array(arr, start, end) <= prev_ending + arr[end - 1]);
                } else {
                    assert(max_ending_here(arr, end) == arr[end - 1]);
                    assert(Sum_Array(arr, start, end - 1) <= 0);
                    assert(Sum_Array(arr, start, end) <= arr[end - 1]);
                }
            }
        };
    }
}

proof fn lemma_max_ending_correctness(arr: Vec<int>, end: int)
    requires 0 < end <= arr.len()
    ensures 
        (exists |start: int| 0 <= start < end && Sum_Array(arr, start, end) == max_ending_here(arr, end)) &&
        (forall |start: int| 0 <= start < end ==> Sum_Array(arr, start, end) <= max_ending_here(arr, end))
{
    lemma_max_ending_here_achievable(arr, end);
    lemma_max_ending_here_is_max(arr, end);
}

// Lemma to establish empty subarray sum
proof fn lemma_empty_subarray(arr: Vec<int>, i: int)
    requires 0 <= i <= arr.len()
    ensures Sum_Array(arr, i, i) == 0
{
    // Base case of Sum_Array definition
}

// Additional helper lemma for transitivity of maximum property
proof fn lemma_max_extends(arr: Vec<int>, i: int, old_max: int, new_ending: int)
    requires 
        0 < i <= arr.len(),
        // old_max was maximum for range [0, i-1]
        (forall |u: int, v: int| 0 <= u && u <= v && v <= i - 1 ==> Sum_Array(arr, u, v) <= old_max),
        // new_ending is maximum for subarrays ending at i
        (forall |u: int| 0 <= u < i ==> Sum_Array(arr, u, i) <= new_ending)
    ensures
        forall |u: int, v: int| 0 <= u && u <= v && v <= i ==> Sum_Array(arr, u, v) <= (if new_ending > old_max { new_ending } else { old_max })
{
    let new_max = if new_ending > old_max { new_ending } else { old_max };
    
    assert forall |u: int, v: int| 0 <= u && u <= v && v <= i implies Sum_Array(arr, u, v) <= new_max by {
        if v < i {
            assert(Sum_Array(arr, u, v) <= old_max);
            assert(Sum_Array(arr, u, v) <= new_max);
        } else if v == i {
            if u == v {
                lemma_empty_subarray(arr, u);
                assert(Sum_Array(arr, u, v) == 0);
                assert(Sum_Array(arr, u, v) <= new_max);
            } else {
                assert(Sum_Array(arr, u, v) <= new_ending);
                assert(Sum_Array(arr, u, v) <= new_max);
            }
        }
    };
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
        lemma_empty_subarray(nums, 0);
        
        // Establish initial invariants
        assert(current_sum == max_ending_here(nums, 1));
        assert(exists |u: int, v: int| 0 <= u && u <= v && v <= 1 && Sum_Array(nums, u, v) == max_sum);
        assert(forall |u: int, v: int| 0 <= u && u <= v && v <= 1 ==> Sum_Array(nums, u, v) <= max_sum);
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
            // current_sum represents max sum ending at position i
            current_sum == max_ending_here(nums, i as int)
    {
        // Compute next values
        let new_current = if current_sum > 0 { current_sum + nums[i] } else { nums[i] };
        let new_max = if new_current > max_sum { new_current } else { max_sum };
        
        proof {
            // Prove new_current equals max_ending_here at i+1
            lemma_max_ending_correctness(nums, (i + 1) as int);
            assert(new_current == max_ending_here(nums, (i + 1) as int));
            
            // Use helper lemma to establish maximum property
            lemma_max_extends(nums, (i + 1) as int, max_sum, new_current);
            
            // Prove new_max is achievable
            if new_current > max_sum {
                // new_current is achievable from max_ending_here property
                lemma_max_ending_here_achievable(nums, (i + 1) as int);
                assert(exists |u: int, v: int| 0 <= u && u <= v && v <= (i + 1) as int && Sum_Array(nums, u, v) == new_max);
            } else {
                // max_sum is still achievable from previous iteration
                assert(exists |u: int, v: int| 0 <= u && u <= v && v <= (i + 1) as int && Sum_Array(nums, u, v) == new_max);
            }
        }
        
        // Update values
        current_sum = new_current;
        max_sum = new_max;
        i += 1;
    }
    
    // Final proof that the postcondition is satisfied
    proof {
        assert(nums.len() > 0);
        assert(0 <= 0 <= nums.len() <= nums.len());
        assert(forall |u: int, v: int| 0 <= u && u <= v && v <= nums.len() ==> Sum_Array(nums, u, v) <= max_sum);
        assert(exists |u: int, v: int| 0 <= u && u <= v && v <= nums.len() && Sum_Array(nums, u, v) == max_sum);
        assert(max_sum_subarray(nums, max_sum, 0, nums.len()));
    }
    
    max_sum
}

}