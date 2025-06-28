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
    
    // Establish initial invariants
    proof {
        lemma_sum_array_single(nums, 0);
        lemma_maximum_subarray_achievable(nums, 1);
        lemma_maximum_subarray_is_max(nums, 1);
    }
    
    let mut i = 1;
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            // max_sum is the maximum subarray sum found so far in range [0, i)
            max_sum == maximum_subarray_sum_up_to(nums, i as int),
            // current_sum is the maximum sum ending at position i-1
            current_sum == max_ending_here(nums, i as int),
            // Invariant: max_sum is achievable by some subarray in range [0, i)
            exists |u: int, v: int| 0 <= u && u <= v && v <= i && Sum_Array(nums, u, v) == max_sum,
            // Invariant: max_sum is maximum among all subarrays in range [0, i)
            forall |u: int, v: int| 0 <= u && u <= v && v <= i ==> Sum_Array(nums, u, v) <= max_sum
    {
        proof {
            lemma_max_ending_here_achievable(nums, i as int);
            lemma_maximum_subarray_achievable(nums, i as int);
            lemma_maximum_subarray_is_max(nums, i as int);
        }
        
        current_sum = if current_sum > 0 { current_sum + nums[i] } else { nums[i] };
        max_sum = if current_sum > max_sum { current_sum } else { max_sum };
        
        proof {
            lemma_max_ending_here_achievable(nums, (i + 1) as int);
            lemma_maximum_subarray_achievable(nums, (i + 1) as int);
            lemma_maximum_subarray_is_max(nums, (i + 1) as int);
        }
        
        i += 1;
    }
    
    // Final proof that max_sum satisfies the postcondition
    proof {
        assert(i == nums.len());
        assert(max_sum == maximum_subarray_sum_up_to(nums, nums.len() as int));
        
        // Prove existence part
        lemma_maximum_subarray_achievable(nums, nums.len() as int);
        assert(exists |u: int, v: int| 0 <= u && u <= v && v <= nums.len() && Sum_Array(nums, u, v) == max_sum);
        
        // Prove maximality part
        lemma_maximum_subarray_is_max(nums, nums.len() as int);
        assert(forall |u: int, v: int| 0 <= u && u <= v && v <= nums.len() ==> Sum_Array(nums, u, v) <= max_sum);
        
        // Therefore max_sum_subarray holds
        assert(max_sum_subarray(nums, max_sum, 0, nums.len()));
    }
    
    max_sum
}

spec fn maximum_subarray_sum_up_to(arr: Vec<int>, end: int) -> int
    requires 0 < end <= arr.len()
    decreases end
{
    if end == 1 {
        arr[0]
    } else {
        let prev_max = maximum_subarray_sum_up_to(arr, end - 1);
        let ending_here = max_ending_here(arr, end);
        if ending_here > prev_max { ending_here } else { prev_max }
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
    assert(Sum_Array(arr, i, i + 1) == arr[i] + Sum_Array(arr, i, i));
    assert(Sum_Array(arr, i, i) == 0);
}

// Helper lemma for subarray properties
proof fn lemma_sum_array_extend(arr: Vec<int>, start: int, stop: int)
    requires 0 <= start <= stop < arr.len()
    ensures Sum_Array(arr, start, stop + 1) == Sum_Array(arr, start, stop) + arr[stop]
{
    // This follows directly from the definition of Sum_Array
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
        if prev_ending > 0 {
            lemma_max_ending_here_achievable(arr, end - 1);
            let start = choose |start: int| 0 <= start < end - 1 && Sum_Array(arr, start, end - 1) == prev_ending;
            lemma_sum_array_extend(arr, start, end - 1);
            assert(Sum_Array(arr, start, end) == Sum_Array(arr, start, end - 1) + arr[end - 1]);
            assert(Sum_Array(arr, start, end) == prev_ending + arr[end - 1]);
            assert(max_ending_here(arr, end) == prev_ending + arr[end - 1]);
        } else {
            lemma_sum_array_single(arr, end - 1);
            assert(Sum_Array(arr, end - 1, end) == arr[end - 1]);
            assert(max_ending_here(arr, end) == arr[end - 1]);
        }
    }
}

// Lemma connecting maximum_subarray_sum_up_to to actual subarrays
proof fn lemma_maximum_subarray_achievable(arr: Vec<int>, end: int)
    requires 0 < end <= arr.len()
    ensures exists |u: int, v: int| 0 <= u && u <= v && v <= end && Sum_Array(arr, u, v) == maximum_subarray_sum_up_to(arr, end)
    decreases end
{
    if end == 1 {
        lemma_sum_array_single(arr, 0);
        assert(Sum_Array(arr, 0, 1) == arr[0]);
        assert(maximum_subarray_sum_up_to(arr, 1) == arr[0]);
    } else {
        let prev_max = maximum_subarray_sum_up_to(arr, end - 1);
        let ending_here = max_ending_here(arr, end);
        if ending_here > prev_max {
            lemma_max_ending_here_achievable(arr, end);
            assert(maximum_subarray_sum_up_to(arr, end) == ending_here);
        } else {
            lemma_maximum_subarray_achievable(arr, end - 1);
            assert(maximum_subarray_sum_up_to(arr, end) == prev_max);
        }
    }
}

// Lemma showing maximum_subarray_sum_up_to is indeed maximum
proof fn lemma_maximum_subarray_is_max(arr: Vec<int>, end: int)
    requires 0 < end <= arr.len()
    ensures forall |u: int, v: int| 0 <= u && u <= v && v <= end ==> Sum_Array(arr, u, v) <= maximum_subarray_sum_up_to(arr, end)
    decreases end
{
    if end == 1 {
        assert(forall |u: int, v: int| 0 <= u && u <= v && v <= 1 ==> {
            (u == 0 && v == 0) || (u == 0 && v == 1)
        });
        lemma_sum_array_single(arr, 0);
        assert(Sum_Array(arr, 0, 0) == 0);
        assert(Sum_Array(arr, 0, 1) == arr[0]);
        assert(maximum_subarray_sum_up_to(arr, 1) == arr[0]);
    } else {
        lemma_maximum_subarray_is_max(arr, end - 1);
        lemma_max_ending_here_is_max(arr, end);
        
        let prev_max = maximum_subarray_sum_up_to(arr, end - 1);
        let ending_here = max_ending_here(arr, end);
        
        assert(forall |u: int, v: int| 0 <= u && u <= v && v <= end ==> {
            if v < end {
                Sum_Array(arr, u, v) <= prev_max
            } else {
                if u < end {
                    Sum_Array(arr, u, v) <= ending_here
                } else {
                    Sum_Array(arr, u, v) == 0
                }
            }
        });
        
        assert(maximum_subarray_sum_up_to(arr, end) >= prev_max);
        assert(maximum_subarray_sum_up_to(arr, end) >= ending_here);
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
        assert(Sum_Array(arr, 0, 1) == arr[0]);
        assert(max_ending_here(arr, 1) == arr[0]);
    } else {
        lemma_max_ending_here_is_max(arr, end - 1);
        let prev_ending = max_ending_here(arr, end - 1);
        
        assert(forall |start: int| 0 <= start < end ==> {
            if start == end - 1 {
                lemma_sum_array_single(arr, start);
                Sum_Array(arr, start, end) == arr[end - 1]
            } else {
                lemma_sum_array_extend(arr, start, end - 1);
                Sum_Array(arr, start, end) == Sum_Array(arr, start, end - 1) + arr[end - 1] &&
                Sum_Array(arr, start, end - 1) <= prev_ending
            }
        });
        
        if prev_ending > 0 {
            assert(max_ending_here(arr, end) == prev_ending + arr[end - 1]);
        } else {
            assert(max_ending_here(arr, end) == arr[end - 1]);
        }
    }
}

}