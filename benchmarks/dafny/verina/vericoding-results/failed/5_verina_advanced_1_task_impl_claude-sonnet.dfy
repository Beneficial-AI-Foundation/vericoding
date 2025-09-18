// <vc-preamble>
// Helper function to count occurrences of an element in a sequence
function CountOccurrences(nums: seq<int>, x: int): nat
{
    |set i | 0 <= i < |nums| && nums[i] == x|
}

// Helper function to filter elements equal to x (recursive implementation)
function FilterEqual(nums: seq<int>, x: int): seq<int>
{
    if |nums| == 0 then []
    else if nums[0] == x then [nums[0]] + FilterEqual(nums[1..], x)
    else FilterEqual(nums[1..], x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lemmas with proper proofs */
function CountOccurrencesInRange(nums: array<int>, x: int, start: int, end: int): nat
    requires 0 <= start <= end <= nums.Length
    reads nums
{
    |set i | start <= i < end && nums[i] == x|
}

lemma CountOccurrencesEquivalence(nums: array<int>, x: int, end: int)
    requires 0 <= end <= nums.Length
    ensures CountOccurrencesInRange(nums, x, 0, end) == CountOccurrences(nums[..end], x)
{
    assert forall i :: 0 <= i < end ==> (nums[i] == x <==> nums[..end][i] == x);
}

lemma CountOccurrencesComplete(nums: array<int>, x: int)
    ensures CountOccurrencesInRange(nums, x, 0, nums.Length) == CountOccurrences(nums[..], x)
{
    assert nums[..nums.Length] == nums[..];
    CountOccurrencesEquivalence(nums, x, nums.Length);
}
// </vc-helpers>

// <vc-spec>
method FindSingleNumber(nums: array<int>) returns (result: int)
    requires 
        nums.Length > 0
    requires
        exists unique_elem :: CountOccurrences(nums[..], unique_elem) == 1
    requires
        forall elem :: elem in nums[..] ==> (CountOccurrences(nums[..], elem) == 1 || CountOccurrences(nums[..], elem) == 2)
    ensures
        CountOccurrences(nums[..], result) == 1
    ensures
        forall x :: x in nums[..] ==> (x == result || CountOccurrences(nums[..], x) == 2)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed syntax error with proper assertion block */
    result := 0;
    var i := 0;
    
    while i < nums.Length
        invariant 0 <= i <= nums.Length
        invariant forall k :: 0 <= k < i ==> CountOccurrences(nums[..], nums[k]) != 1
    {
        var count := 0;
        var j := 0;
        ghost var target := nums[i];
        
        while j < nums.Length
            invariant 0 <= j <= nums.Length
            invariant target == nums[i]
            invariant count == CountOccurrencesInRange(nums, target, 0, j)
        {
            if nums[j] == target {
                count := count + 1;
            }
            j := j + 1;
        }
        
        CountOccurrencesComplete(nums, target);
        assert count == CountOccurrences(nums[..], target);
        
        if count == 1 {
            result := nums[i];
            assert CountOccurrences(nums[..], result) == 1;
            assert forall x :: x in nums[..] ==> (x == result || CountOccurrences(nums[..], x) == 2) by {
                forall x | x in nums[..]
                    ensures x == result || CountOccurrences(nums[..], x) == 2
                {
                    if x != result {
                        assert CountOccurrences(nums[..], x) != 1;
                        assert CountOccurrences(nums[..], x) == 1 || CountOccurrences(nums[..], x) == 2;
                        assert CountOccurrences(nums[..], x) == 2;
                    }
                }
            }
            return;
        }
        
        i := i + 1;
    }
    
    // This should never be reached due to preconditions
    assert false;
}
// </vc-code>
